from sympy  import*
from sympy  import itermonomials as itm
import time
import numpy as np

"""
Sympy implementation of ACons algorithm accompanying the thesis: 'Algorithms for the
symbolic computation of differential invariants, the case of PDEs'

The required Sympy version is 1.1.1

The main functions are:
- A(pt) that returns sigma formal invariants of the form of pt 
- findConservationLaws(var, degree) that finds sigma conservation laws as maximum 
grade degree polynomials in var variables.

Examples illustrated in the thesis are at the end of the script.
"""


#----------invariant computation------------
def derutau(utau,j):
    s= str(utau)  # utau as a string
    ordj=int(s[j])   
    der= var(s[:j]+str(ordj+1)+s[j+1:])
    if(isPrincipal(der))==true:
    	principalDer.append(der)
    else:
    	parametricDer.append(der)
    return der 

def mydifftotal(expr, diffby):
    j=indlist.index(diffby)+1
    utauset=expr.free_symbols.intersection(set(parametricDer+principalDer))
    diffmap={utau:derutau(utau,j) for utau in utauset}
    # Replace all symbols in the diffmap by a functional form
    fnexpr = expr.subs({utau:utau(diffby) for utau in utauset})
    # Do the differentiation
    diffexpr = diff(fnexpr, diffby)
    # Replace the Derivatives with the variables in diffmap
    derivmap = {Derivative(v(diffby), diffby):dv for v,dv in  (diffmap.items())}
    finaldiff = diffexpr.subs(derivmap)
    #takes the total derivative of an expression exp with respect to variable diffby
    return finaldiff.subs({utau(diffby):utau for utau in diffmap}) 


def isPrincipal(u):
    su=str(u)
    for k in sigma:
        sk=str(k)
        der=true
        if su[0]==sk[0]:
            for i in range(1,len(sk)):
                if (su[i]<sk[i]):
                    der=false
            if(der==true):
                return true #returns true if u is a principal derivative
    return false
		

def findBestDer(u):
    su=str(u)
    tot=100000
    rst=''
    for k in sigma:
        temp=0
        sk=str(k)
        if su[0]==sk[0]:
            for i in range(1,len(su)):
                diff=int(su[i])-int(sk[i])
                
                if(diff>=0):
                    temp=temp+diff
                else: 
                    temp=tot
                    break
            if temp<tot:
                tot=temp
                rst=k #rst is the closest derivative to u in Sigma 
    return rst

def startDerivate(a, b):
    derList=[]
    for i in range(1,len(str(a))):
        derList.append(int(str(b)[i])-int(str(a)[i]))		
    sa=sigma[a]
    for i in range(0,len(derList)):
        n=derList[i]
        while n>0:
            a=mydifftotal(a, indlist[i])
            sa=mydifftotal(sa, indlist[i])
            n=n-1
    return sa
			
def reduceSigma(): 
    stable=False
    while not stable:
        items=list(sigma.items())  
        stable=True
        for k, v in items:
            rst=reduceEq(k,v)
            if rst!=v:
                stable=False 
                sigma[k]=rst #returns an autoreduced Sigma


def reduceEq(k,v): #applies normal form function to sigma equations
    derlist=list(Add(v,0).free_symbols.intersection(set(principalDer))) 
    if derlist==[]:
        return v
    for der in derlist:
        if der in sigma.keys():
            v=v.subs(der,sigma[der])
        else:
            bestDer=findBestDer(der)
            finalSub=startDerivate(bestDer,der)
            v=v.subs(der, finalSub)
            sigma[der]=finalSub 
    return reduceEq(k,v)

def completeSigma(ptder):
    for actualder in ptder:    
        if actualder not in sigma.keys():
            bestDer=findBestDer(actualder)
            finalSubs=startDerivate(bestDer,actualder)
            sigma[actualder]=finalSubs

def computeS(pt,ptder):  #applies normal form function to pt
    return pt.subs({q:sigma[q] for q in ptder}) 

	
def genpt(Xlist,deg,offset=0): 
    monlist=list(itm(Xlist,deg))
    l=len(monlist)
    parlist = list(var('a%d' % j) for j in range(offset,l+offset))
    prod=(Matrix(monlist).T *Matrix(parlist))[0,0]
    return prod, parlist #returns polynomial template and its parameters

def resolve(lincf,pl):  #solves linear equations 
    sigma=[]
    lc=str(len(lincf))
    start_timedict = time.time()
    print("     Start building dict...")
    dicta={ a:set([j for j in range(len(lincf)) if a in lincf[j].free_symbols ]) for a in pl }
    print("     Elapsed time(dict): %s seconds ---" % (time.time() - start_timedict))
    start_timelinear = time.time()
    print("     Start solving linear expressions...")    
    for j in range(len(lincf)):
        lin=lincf[j]
        sd=solve([lin],solution_dict=True)
        if type(sd)==type({}):
            s=sd
            sigma=sigma+(list(s.items()))
        elif (type(sd)==type([])) & (sd!=[]):
            s=sd[0]
            sigma=sigma+(list(s.items()))
        else:
            s={}
        if s!={}:
            a=list(s.keys())[0]
            aset=s[a].free_symbols
            A=np.array(list(dicta[a]))
            for i in A[A>j]:
                lincf[i]=lincf[i].subs(s)
                for b in aset:
                    dicta[b]=dicta[b].union({i})
        print("\r", "     "+str(j+1)+" out of "+lc+" linear expressions solved...    ", end ="")
    print("")
    print("     Elapsed time solving linear expressions: %s seconds ---" % (time.time() - start_timelinear)) 
    return sigma                    
                    
def A(pt,returnpt=True): #computes formal invariants
    print('  invoke A...')
    global indlist, parametricDer, principalDer
    start_A_time= time.time()
    #principal derivative of pt
    ptder=list(pt.free_symbols.intersection(set(principalDer)))
    
    completeSigma(ptder)
    
    #autoreduces sigma
    reduceSigma()
    
    #computes S(pt) 
    qt=computeS(pt,ptder)
    
    #generators list
    gl= list(set(indlist+parametricDer+principalDer))
    #polynomial template
    qt=Poly(qt,gl)
    #coefficients
    cf=qt.coeffs()
    
    #finds substitution
    nullsubs=resolve(cf,qt.free_symbols.difference(set(indlist+parametricDer+principalDer)))  
    
    if returnpt:
        print('  A time lapse:',time.time()-start_A_time)	
        return qt, nullsubs 
    else:
        print('  A time lapse:',time.time()-start_A_time)	
        return nullsubs 

#----------------------conservation laws-----------------------
def findBase(param,subptlist):	  
    polyptlist=[Poly(pt ,param) for pt in subptlist]
    m=len(param)    
    zeroarg=[0]*m
    final_base=[]
    for j in range(m):
        sigmaj=zeroarg.copy()
        sigmaj[j]=1
        final_base.append([pt(*sigmaj)  for pt in polyptlist]  )
    return final_base
	
	 
def find_param(subptlist,parlist):
    param=set()
    for el in subptlist:
        param.update(el.free_symbols)
    return list(param.intersection(set(parlist)))

def seqsub(sigma,pt):   # sequentially applies a list of substitutions in sigma to template pt
    for s in sigma:
        pt=pt.subs(s)
    return pt

#finds conservation laws as maximum grade degree polynomials in var variables
def findConservationLaws(var, degree): 
    start_cons_time = time.time()
    dpt=0
    offset=0
    parlist=[] #parameter list
    ptlist=[] #template list
    print('  start divergence template construction...')
    start_template_time = time.time()
    for i in range(len(indlist)):
        temp, temppl=genpt(var, degree, offset)
        ptlist.append(temp)
        parlist=parlist+temppl
        dpt=dpt+mydifftotal(temp,indlist[i])
        offset=offset+len(temppl)
    print('  divergence template time:',time.time()-start_template_time)
        
    #finds substitution t.c. S(dpt)=0
    s = A(dpt,False)
    
    #applies substitution to ptlist
    print('  apply substitution on densities templates...') 
    start_subs_time = time.time()
    subptlist=[]
    ssim=seq2sim(s)
    for pt in ptlist:
        plpt=list(pt.free_symbols.intersection(parlist))
        ptd=Poly(pt,plpt).as_dict()
        res=0
        for a in ptd.keys():
            ptda=ptd[a]
            ai=plpt[a.index(1)]
            if ai in ssim.keys():
                res=res+ssim[ai]*ptda
            else:
                res=res+ai*ptda
        subptlist.append(res)
    print('  substitutions on densities templates time:',time.time()-start_subs_time)        
    
    print('  find left parameters...')
    start_param_time = time.time()
    param=find_param(subptlist,parlist)
    print('  find left parameters time lapse:',time.time()-start_param_time)
    
    print('  start base construction...')
    start_base_time = time.time()
    final_base=findBase(param,subptlist)   
    print('  base construction time lapse:',time.time()-start_base_time)
    print('Conservation laws time lapse:',time.time()-start_cons_time)
    return final_base
    
    
def seq2sim(s):
    ssim={}
    for x,e in s:
        for k in ssim.keys():
            v=ssim[k]
            ssim[k]=v.subs({x:e})
        ssim[x]=e
    return ssim
    
def firstKind_check(p): #returns true if p is a first-type law
    for i in range(len(indlist)):
        ptder=list(p[i].free_symbols.intersection(set(principalDer)))
        sp=computeS(p[i],ptder)
        if sp!=0:   
            return false
    return true

def secondKind_check(p): #returns true if p is a second-type law
    dpt=0
    for i in range(len(indlist)):
        dpt=dpt+mydifftotal(p[i],indlist[i])
    if dpt==0:    
        return true
    return false

def filter(p_list): #filters trivial laws from p_list
    start_filter_time = time.time()
    filtered_list=[]
    for p in p_list:
        if not firstKind_check(p) and not secondKind_check(p) :
            filtered_list.append(p)
    print('Filter trivial laws time lapse:',time.time()-start_filter_time)
    return filtered_list


#-----------support functions-----------------------

from collections import Iterable
def initvar(indepX,dependU,listutau):  #declares variables and derivatives
    global indlist, ulist, utaulist   
    indlist=var(indepX)
    if isinstance(indlist, Iterable):
        indlist=list(indlist)
    else:
        indlist=[indlist]
    ulist=  var(dependU) 
    if isinstance(ulist, Iterable):
        ulist=list(ulist)
    else:
        ulist=[ulist]
    utaulist= var(listutau) 
    if isinstance(utaulist, Iterable):
        utaulist=list(utaulist)
    else:
        utaulist=[utaulist]

    
def initSigma(Sigma):  #initializes sigma
    global utaulist, sigma, parametricDer, principalDer
    sigma=Sigma
    parametricDer=[]
    principalDer=[]
    for utau in utaulist:
        if isPrincipal(utau):
            principalDer.append(utau)
        else:
            parametricDer.append(utau)

def checkLinDep(D,F,Base): 
    global indlist, parametricDer, principalDer
    parametricDer = list(set(parametricDer))
    principalDer= list(set(principalDer))
    xlist=indlist+parametricDer+principalDer
    if (D,F) in Base:
        return [(1,(D,F),Base.index((D,F)))]
    clist=list(var('c%d' % j) for j in range(len(Base)))
    A=sum([c*d[0] for c,d in zip(clist,Base)])
    AP=Poly(A-D,xlist)
    cf=AP.coeffs()
    sigmaA=solve(cf,dict=True)
    if len(sigmaA)==0 and  (D!=0) and (F!=0):
        print('no linear dependence')
        return False
    B=sum([c*d[1] for c,d in zip(clist,Base)])
    BP=Poly(B-F,xlist)
    BPA=Poly(BP.subs(sigmaA[0]),xlist)
    cfB=BPA.coeffs()
    sigmaB=solve(cfB,dict=True)
    if len(sigmaB)==0 and  (D!=0) and (F!=0):
        return False
    res=[(clist[i].subs(sigmaA[0]).subs(sigmaB[0]),Base[i],i) for i in range(len(clist)) if clist[i].subs(sigmaA[0]).subs(sigmaB[0])!=0]
    print('linear dep.:',res)
    return res #true if there is a linear dipendence between D and F

def normalizeLaw(law): #computes S(law)
    res=[]
    for el in law:
        ptder=list(el.free_symbols.intersection(set(principalDer)))
        res.append(computeS(el, ptder))
    return res
         
         
  
#----------------------------------------------------------------------
#----------------------------Experiments--------------------------------
#----------------------------------------------------------------------
#Experiments are made using four classic PDEs of Mathematical physics: Korteweg-de Vries,
#Boussinesq, Drinfel'd-Sokolv-Wilson and sine-Gordon.  
'''
#------------Korteweg-de Vries

print('EXAMPLE: Korteweg-de Vries \t')
initvar('t x','u','u00 u10 u01 u03 u02 u04')  
deVries={u10:-u00*u01-u03}   # fisso alfa=1
initSigma(deVries)

#Anstaz1
con_deVries=findConservationLaws([u00, u01, u02, u03],2) #finds conservation laws
filtered_laws=filter(con_deVries) #filters trivial laws
print('---Ansatz1: \t')
qt=normalizeLaw([(u00**3+3*u00*u02)/6, u01*u10/2+u00**2*u02/2+u00**4/8+u02**2/2-u00*u11/2 ])  #normalizes the law taken as input
checkLinDep(qt[0], qt[1], con_deVries) 
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries) #check if the first law is a linear combination of some of the ACons laws 
checkLinDep(u00, u00**2/2+u02, con_deVries)
print('law\'s number:',len(filtered_laws)) #laws number

#Anstaz2
con_deVries=findConservationLaws([t,x, u00, u01, u02, u03],2)
filtered_laws=filter(con_deVries) 
print('---Ansatz2: \t')
qt=normalizeLaw([(u00**3+3*u00*u02)/6, u01*u10/2+u00**2*u02/2+u00**4/8+u02**2/2-u00*u11/2]) #no
checkLinDep(qt[0], qt[1], con_deVries)
checkLinDep(-u00**2*t/2+u00*x,(-2*u00**3-6*u00*u02+3*u01**2)*t/6+u00**2*x/2+u02*x-u01, con_deVries)
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries)
checkLinDep(u00, u00**2/2+u02, con_deVries)
print('law\'s number:',len(filtered_laws))

#Anstaz3
con_deVries=findConservationLaws([t,x, u00, u01, u02, u03,u04],2)
filtered_laws=filter(con_deVries) 
print('---Ansatz3: \t')
qt=normalizeLaw([(u00**3+3*u00*u02)/6, u01*u10/2+u00**2*u02/2+u00**4/8+u02**2/2-u00*u11/2 ])
checkLinDep(qt[0], qt[1], con_deVries)
checkLinDep(-u00**2*t/2+u00*x,(-2*u00**3-6*u00*u02+3*u01**2)*t/6+u00**2*x/2+u02*x-u01, con_deVries)
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries)
checkLinDep(u00, u00**2/2+u02, con_deVries)
qt=normalizeLaw([u00*(5*u00**3+40*u00*u02+20*u01**2+36*u04)/120, u00**5/30+u02*u00**3/6+(15*u01**2-20*u11)*u00**2/60+((20*u01*36*u04)*u01+12*u02**2-18*u13)*u00/60-u01**2*u02/10+3*u12*u01/10-3*u02*u11/10+3*u03*(u10+u03)/10])
checkLinDep(qt[0], qt[1], con_deVries)
print('law\'s number:',len(filtered_laws))

#-------------Boussinesq

print('EXAMPLE: Boussinesq \t')
initvar('t x','u v','u00 u04 u10 u01 u03 u02 v01 v10 v02 v00')  
boussinesq={u10:-v01, v10:-u01+3*u00*u01+u03 }   # fisso beta=1
initSigma(boussinesq)

#Anstaz1
con_bouss=findConservationLaws([u00,u01,u02,v00, v01],2)
filtered_laws=filter(con_bouss)
print('---Ansatz1: \t')
checkLinDep( u00,v00,con_bouss)
checkLinDep( v00, -3*u00**2/2+u00-u02, con_bouss)
qt=normalizeLaw([-u00**3/2+u00**2/2-u02*u00/2+v00**2/2,-3*u00**2*v00/2+(2*v00+u11)*u00/2-v00*u02-u01*u10/2 ])#no
checkLinDep(qt[0], qt[1], con_bouss)
print(qt[0])
print(qt[1])
checkLinDep(u00*v00, -u00**3+v00**2/2+u00**2/2-u02*u00+u01**2/2,con_bouss)
print('law\'s number:',len(filtered_laws))

#Anstaz2
con_bouss=findConservationLaws([t,x,u00,u01,u02,u03,v00, v01],2)
filtered_laws=filter(con_bouss)
print('---Ansatz2: \t')
checkLinDep( u00,v00,con_bouss)
checkLinDep( v00, -3*u00**2/2+u00-u02, con_bouss)
qt=normalizeLaw([-u00**3/2+u00**2/2-u02*u00/2+v00**2/2,-3*u00**2*v00/2+(2*v00+u11)*u00/2-v00*u02-u01*u10/2 ])
checkLinDep(qt[0], qt[1], con_bouss)
print(qt[0])
print(qt[1])
checkLinDep(-u00*x+v00*t, (-3*u00**2+2*u00-2*u02)*t/2-v00*x,con_bouss)#no
checkLinDep(u00*v00, -u00**3+v00**2/2+u00**2/2-u02*u00+u01**2/2,con_bouss)
print('law\'s number:',len(filtered_laws))

#Anstaz3
con_bouss=findConservationLaws([t,x,u00,u01,u02,u03,u04,v00, v01,v02],2)
filtered_laws=filter(con_bouss)
print('---Ansatz3: \t')

checkLinDep( u00,v00,con_bouss)
checkLinDep( v00, -3*u00**2/2+u00-u02, con_bouss)
checkLinDep( -u00*x+v00*t, (-3*u00**2/2+u00-u02)*t-v00*x, con_bouss)
qt=normalizeLaw([-u00**3/2+u00**2/2-u02*u00/2+v00**2/2,-3*u00**2*v00/2+(2*v00+u11)*u00/2-v00*u02-u01*u10/2 ])
checkLinDep(qt[0], qt[1], con_bouss)
print(qt[0])
print(qt[1])
checkLinDep(u00*v00, u00**2/2-u00**3-u02*u00+u01**2/2+v00**2/2, con_bouss)
qt=normalizeLaw([-u00**4/4+u00**3/6-u02*u00**2+(-6*u01**2+6*v00**2+4*u02-4*u04)*u00/12+v00*v02/3, -v00*u00**3+(3*v00+6*u11)*u00**2/6
+((-6*u10-12*v01)*u01-6*v00*u02+2*u13-2*u11)*u00/6+v00*u01**2/2+(-2*u12+2*u10+4*v01)*u01/6+v00**3/6-v00*v11/3+
(-4*u03+2*v10)*v01/6-u10*u03/3+u02*u11/3]) #no
    
checkLinDep(qt[0], qt[1], con_bouss)
print('law\'s number:',len(filtered_laws))

#-------------DSW

print('EXAMPLE: DSW \t')
initvar('t x','u v','u00 u10 u01 v01 v10 v00 v02 v03 u02 v04')  
dsw={u10:-3*v00*v01, v10:-2*u00*v01-u01*v00-2*v03 }   # fisso alfa=1
initSigma(dsw)

#Anstaz1
con_dsw=findConservationLaws([u00, u01, v00, v01,v02],2)
filtered_laws=filter(con_dsw) 
print('---Ansatz1: \t')
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
print('law\'s number:',len(filtered_laws))

#Anstaz2
con_dsw=findConservationLaws([t,x,u00, u01,v00, v01,v02,v03],2)
filtered_laws=filter(con_dsw) 
print('---Ansatz2: \t')
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
checkLinDep(-3*v00**2*t/2+u00*x, (-6*u00*t+3*x)*v00**2/2-6*v00*t*v02+3*v01**2*t,con_dsw)
print('law\'s number:',len(filtered_laws))

#Anstaz3
con_dsw=findConservationLaws([t,x,u00, u01,u02,v00, v01,v02,v03,v04],2)
filtered_laws=filter(con_dsw) 
print('---Ansatz3: \t')
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
checkLinDep(-3*v00**2*t/2+u00*x, (-6*u00*t+3*x)*v00**2/2-6*v00*t*v02+3*v01**2*t,con_dsw)
qt=normalizeLaw([2*u00**3/3+(-18*v00**2+3*u02)*u00/6-9*v02*v00/2, -9*v00**4/4-3*u00**2*v00**2+(-48*u00*v02+12*v01*u01+18*v11)*v00/4+(-12*v01**2-2*u11)*u00/4+u01*u10/2-9*v01*v10/2-9*v02**2 ])
checkLinDep(qt[0], qt[1], con_dsw)
print('law\'s number:',len(filtered_laws))


#------------sine-Gordon

print('EXAMPLE: sine-Gordon \t')
initvar('t x','u v s c','u00 u10 u01 u02 v01 v10 v00 v02 u03 v03 c01 s01 c10 s10 c00 s00')  
gordon={u10:-v00, v10:-u02-s00, s10:c00*u10, c10:-s00*u10, s01:c00*u01, c01:-s00*u01}   # fisso alfa=1
initSigma(gordon)

#A1
con_sg=findConservationLaws([u00, u01,v00,c00],4)
filtered_laws=filter(con_sg) 
print('---Ansatz1: \t')
print('law\'s number:',len(filtered_laws))


#A2
con_sg=findConservationLaws([u00, u01,u02,v00,v01,c00],4)
filtered_laws=filter(con_sg) 
qt=normalizeLaw([v00**2/2+u01**2/2+c00,-u10*u01])
checkLinDep(qt[0], qt[1], con_sg)
qt=normalizeLaw([-(v10+u00)*v01, -c00+v00*v10*t+u00*v10+u01**2/2])
print('---Ansatz2: \t')
checkLinDep(qt[0], qt[1], con_sg)
print('law\'s number:',len(filtered_laws))


#A3
con_sg=findConservationLaws([t,x,u00, u01,u02, v00,v01,c00],4)
filtered_laws=filter(con_sg) 
print('---Ansatz3: \t')
#qt=normalizeLaw([-(v00*t+u00)*v01, -c00+v00*v10*t+u00*v10+u01**2/2])
#print(checkLinDep(qt[0], qt[1], con_sg))
print('law\'s number:',len(filtered_laws))


#---------------other tests

initvar('t x','u','u00 u10 u01 u03 u02 u04')  
deVries={u10:-u00*u01-u03}   # fisso alfa=1
initSigma(deVries)
con_deVries=findConservationLaws([u00, u01, u02, u03],2)
filtered_laws=filter(con_deVries) 
qt=normalizeLaw([u00*(5*u00**3+40*u00*u02+20*u01**2+36*u04)/120, u00**5/30+u02*u00**3/6+(15*u01**2-20*u11)*u00**2/60+((20*u01*36*u04)*u01+12*u02**2-18*u13)*u00/60-u01**2*u02/10+3*u12*u01/10-3*u02*u11/10+3*u03*(u10+u03)/10])
checkLinDep(qt[0], qt[1], con_deVries)
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries)
checkLinDep(u00, u00**2/2+u02, con_deVries)
print('law\'s number:',len(filtered_laws))


initvar('t x','u v','u00 u04 u10 u01 u03 u02 v01 v10 v02 v00')  
boussinesq={u10:-v01, v10:-u01+3*u00*u01+u03 }   # fisso beta=1
initSigma(boussinesq)
con_bouss=findConservationLaws([u00,u01,u02,u03,v00, v01],2)
filtered_laws=filter(con_bouss)
qt=normalizeLaw([--u00**4/4+u00**3/6-u02*u00**2+(-6*u01**2+6*v00**2+4*u02-4*u04)*u00/12+v00*v02/3, -v00*u00**3+(3*v00+6*u11)*u00**2/6
+((-6*u10-12*v01)*u01-6*v00*u02+2*u13-2*u11)*u00/6+v00*u01**2/2+(-2*u12+2*u10+4*v01)*u01/6+v00**3/6-v00*v11/3+
(-4*u03+2*v10)*v01/6-u10*u03/3+u02*u11/3])
checkLinDep(qt[0], qt[1], con_bouss)
checkLinDep(u00*v00, -u00**3+v00**2/2+u00**2/2-u02*u00+u01**2/2,con_bouss)
qt=normalizeLaw([-u00**3/2+u00**2/2-u02*u00/2+v00**2/2,-3*u00**2*v00/2+(2*v00+u11)*u00/2-v00*u02-u01*u10/2 ])
checkLinDep( v00, -3*u00**2/2+u00-u02, con_bouss)
checkLinDep( u00,v00,con_bouss)
print('law\'s number:',len(filtered_laws))


initvar('t x','u v','u00 u10 u01 v01 v10 v00 v02 v03 u02 v04')  
dsw={u10:-3*v00*v01, v10:-2*u00*v01-u01*v00-2*v03 }   # fisso alfa=1
initSigma(dsw)
con_dsw=findConservationLaws([u00, u01,v00, v01,v02,v03],2)
filtered_laws=filter(con_dsw) 
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
qt=normalizeLaw([2*u00**3/3+(-18*v00**2+3*u02)*u00/6-9*v02*v00/2, -9*v00**4/4-3*u00**2*v00**2+(-48*u00*v02+12*v01*u01+18*v11)*v00/4+(-12*v01**2-2*u11)*u00/4+u01*u10/2-9*v01*v10/2-9*v02**2 ])
checkLinDep(qt[0], qt[1], con_dsw)
print('law\'s number:',len(filtered_laws))


initvar('t x','u v s c','u00 u10 u01 u02 v01 v10 v00 v02 u03 v03 c01 s01 c10 s10 c00 s00')  
gordon={u10:-v00, v10:-u02-s00, s10:c00*u10, c10:-s00*u10, s01:c00*u01, c01:-s00*u01}   # fisso alfa=1
initSigma(gordon)
con_sg=findConservationLaws([u00, u01,v00,c00],2)
filtered_laws=filter(con_sg) 
print('law\'s number:',len(filtered_laws))
'''










 
