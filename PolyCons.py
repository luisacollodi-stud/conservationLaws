from sympy  import*
from sympy  import itermonomials as itm
import time
import numpy as np
import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning) 


"""
SymPy implementation of PolyCons, an algorithm for the symbolic computation of PDE polynomial conservation laws.
See the paper:
M. Boreale, L. Collodi. A linear-algebraic method to compute polynomial PDE conservation laws. 2020.

**Important: requires SymPy version 1.1.1. Will not work on newer versions. **
  To downgrade SymPy, from the OS command prompt, issue: 
      pip install sympy==1.1.1
  To upgrade SymPy after trying the code, from the OS command prompt, issue: 
      pip install sympy --upgrade
  (NB: pip may require administrator privileges).
  
  
The main functions are:   

    - initvar(indVars,depVars,derList):  declares independent and dependent variables and a list of corresponding derivatives (see examples below)
    
    - initSigma(Equations): declares a system of PDEs in the previously introduced variables (see examples below)
    
    - findConservationLaws(var, degree): returns a basis for the vector space of the system's polynomial conservation laws 
                                         up to a specified degree and with variables in the list var. 
                                   
    - filter(p_list):  given a list p_list conservation laws (n-uples of fluxes) filters out the 
                                       trivial ones, and retuns the nontrivial laws.
    

         
  
Only deals with "leading linear" systems (leading derivative in linear form). An example of usage is the following.             

Fixing an order for the independent variables X=(t,x), we represent the derivatives u_{t^i x^j} as strings 'uij',
with i,j nonnegative integers.
Example. Consider the case of the wave equation in (1+1)D: u_{tt}=u_{xx}. We have:                           

initvar('t x','u','u00 u10 u20 u01 u02')  # declares variables
Wave={u20:u02}  # encodes the PDE system for which the conservation laws are to be computed ((1+1)D wave equation) 
initSigma(Wave)   # initializes the global variable sigma, the system, and the list of its principal and parametric derivatives 
con_lawsWave=findConservationLaws([u10, u01],2) # computes a basis for the vector space of all polynomial conservation laws (fluxes) of Wave up to degree 2, in the differential indeterminates u_x, u_t
filtered_laws=filter(con_lawsWave)  # filters out trivial laws from the basis and returns the nontrivial ones


Additional examples are at the end of the script.                            


"""


#----------invariant computation------------
def derutau(utau,j):
    '''
    It computes the partial derivative of a dipendent variable with respect to an independent variable.
    
         Args:
             - utau: symbol, representing a dipendent variable
             - j: integer, the index that identifies the independent variable from which we wants to derive
         
         Returns:
            - the symbol representing the derivative of utau
    '''
    s= str(utau)  
    ordj=int(s[j])   
    der= var(s[:j]+str(ordj+1)+s[j+1:])
    if(isPrincipal(der))==true:
    	principalDer.append(der)
    else:
    	parametricDer.append(der)
    return der 

def mydifftotal(expr, diffby):
    '''
    It computes the total derivative of an expression with respect to an indipendent variable.
        
        Args:
            - expr: SymPy expression, representing a polynomial
            - diffby: symbol, representing the independent variable from which we wants to derive
            
        Returns:
            - SymPy expression, representing the total derivative of expr with respect to diffby 
    ''' 
    if  type(expr)==int:
        return 0
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
    '''
    It checks if a given derivative is principal or parametric.
    
        Args:
            - u: symbol, representing the derivative to check
            
        Returns:
            - boolean, true if u is a principal derivative
    '''
    su=str(u)
    for k in sigma:
        sk=str(k)
        der=true
        if su[0]==sk[0]:
            for i in range(1,len(sk)):
                if (su[i]<sk[i]):
                    der=false
            if(der==true):
                return true 
    return false
		

def findBestDer(u): 
    '''
    It finds among all the derivatives present in the sigma system the 'closest' to u,
    in terms of derivation orders. 
    
        Args:
            - u: symbol, representing the derivative to analyze
            
        Returns:
            - symbol, the closest derivative to u in sigma 
    '''
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
                rst=k  
    return rst

def startDerivate(a, b): 
    '''
    It derives the sigma equation that contains 'a' until 'a' becomes equal to 'b'.
    
        Args:
            - a: symbol, representing a derivative 
            - b: symbol, representing the target derivative
            
        Returns:
            - expression, representing the modified equation 
    '''
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
    '''
    It makes sigma autoreduced, that is without principal derivatives in the right part of its equations.
    '''
    stable=False
    while not stable:
        items=list(sigma.items())  
        stable=True
        for k, v in items:
            rst=reduceEq(k,v)
            if rst!=v:
                stable=False 
                sigma[k]=rst #returns an autoreduced Sigma


def reduceEq(k,v): 
    '''
    It applies normal form function to an equation.
        
        Args:
            - k: symbol, representing the left part of the considered equation
            - v: expression, representing the right part of the considered equation
            
        Returns:
            - v: expression, representing v without principal derivatives
    '''
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
    '''
    It completes sigma system with equations whose main term is one of the derivatives in ptder, 
    if they aren't present yet. 
    
        Args:
            - ptder: list of symbols, representing derivatives
    '''
    for actualder in ptder:    
        if actualder not in sigma.keys():
            bestDer=findBestDer(actualder)
            finalSubs=startDerivate(bestDer,actualder)
            sigma[actualder]=finalSubs

def computeS(pt,ptder): 
    '''
    It applies normal form function to a polynomial.
    
        Args:
            - pt: expression, representing the polynomial to normalize
            - ptder: list of symbols, representing the principl derivatives of pt
            
        Returns:
            - the normalized polynomial
    '''
    completeSigma(ptder)
    return pt.subs({q:sigma[q] for q in ptder}) 

	
def genpt(Xlist,deg,offset=0): 
    '''
    It generates a polynomial template.
    
        Args:
            - Xlist: list of symbols, representing the variables of the polynomial template
            - deg: integer, that is the degree of the polynomial template
            - offset: integer, useful for changing the numbering of parameters
            
        Returns:
            - prod: expression, representing the polynomial template
            - parlist: list of symbols, containing the parameters of prod
    '''
    monlist=list(itm(Xlist,deg))
    l=len(monlist)
    parlist = list(var('a%d' % j) for j in range(offset,l+offset))
    prod=(Matrix(monlist).T *Matrix(parlist))[0,0]
    return prod, parlist 

def resolve(lincf,pl):  #solves linear equations 
    '''
    It resolves linear equations.
    
        Args:
            - lincf: list of expressions, representing equations to solve
            - pl: set of symbols, containing all the parameters of lincf
        
        Returns:
            - a list of tuples representing all the equations solutions
    '''
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
                    
def invariant(pt,returnpt=True):  
    '''
     It finds a parameters substitution for the polynomial template taken as input, such that it is 
     an invariant polynomial, for each value of its remaining parameters. 
  
         Args:
             - pt: SymPy expression with variables and parameters, representing a polynomial template
             - returnpt: boolean variable, if true, the function returns both the new polynomial template after the 
                         parameter substitution and the substitution, if false, it returns only the substitution
           
         Returns:
             - pt_new: Poly object, representing the polynomial template after the parameter substitution
             - subs: list of tuples, representing a substitution for pt parameters such that pt is an invariant
    '''
    print('  invoke normalization...')
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
        print('  Normalization time lapse:',time.time()-start_A_time)	
        return qt, nullsubs 
    else:
        print('  Normalization time lapse:',time.time()-start_A_time)	
        return nullsubs 

#----------------------conservation laws-----------------------
def findBase(param,subptlist): 
    '''
    It finds a base for subtlist.
    
        Args:
            - param: list of symbols, that are the parameters of subtlist
            - subptlist: list of parametric expressions, representing a vector space
            
        Returns:
            - a list of expressions lists, that is a base for the vector space described by subptlist        
    '''
    polyptlist=[Poly(pt ,param) for pt in subptlist]
    m=len(param)    
    zeroarg=[0]*m
    final_base=[]
    for j in range(m):
        sigmaj=zeroarg.copy()
        sigmaj[j]=1
        final_base.append([pt(*sigmaj)  for pt in polyptlist]  )
    return final_base
	
	 
def find_param(subptlist,parlist): #returns parlist variables that are present in subptlist polynomial
    '''
    It identifies the set of parameters that are contained in the second argument, and that appear in the first one.
    
        Args:
            - subptlist: list of parametric expressions
            - parlist: list of symbols, that are the parameters of subptlist
        
        Returns:
            - a list of symbols, that is the set of parameters of parlist that are present in subptlist
            
    '''
    param=set()
    for el in subptlist:
        param.update(el.free_symbols)
    return list(param.intersection(set(parlist)))


def findConservationLaws(var, degree): 
    '''
     It computes a basis for vector space of the polynomial conservation laws for the system we are analyzing, 
         up to a specified degree.
                   
         Args:
             - var: list of variables, in which laws have to be found
             - degree: integer, representing the highest degree of the laws we are looking for
           
         Returns:
             - laws: list of expressions lists, representing a basis for all the polynomial conservation laws
                     of the considered system

    '''
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
        
    #finds substitution s.t. S(dpt)=0
    s = invariant(dpt,False)
    
    #applies substitution to ptlist
    print('  apply substitution to flux templates...') 
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
    final_base=findBase(param,subptlist)   #finds a base for sigma polynomial conservation laws
    print('  base construction time lapse:',time.time()-start_base_time)
    print('Conservation laws time lapse:',time.time()-start_cons_time)
    return final_base
    
    
def seq2sim(s): 
    '''
    It converts the list taken as input into a dictionary
    
        Args:
            - s: list of tuples
                
        Returns:
            - the dictionary corresponding to the s list
    '''
    ssim={}
    for x,e in s:
        for k in ssim.keys():
            v=ssim[k]
            ssim[k]=v.subs({x:e})
        ssim[x]=e
    return ssim
    
def firstKind_check(p):
    '''
    It checks if a conservation law is of the first type.
    
        Args:
            - p: list of expressions, representing the conservation law we are analyzing
        
        Returns:
            - a boolean variable, it's true is p is a first type conservation law, false otherwise
    '''
    for i in range(len(indlist)):
        ptder=list(p[i].free_symbols.intersection(set(principalDer)))
        sp=computeS(p[i],ptder)
        if sp!=0:  
            return false
    return true

def secondKind_check(p): 
    '''
    It checks if a conservation law is of the second type.
    
        Args:
            - p: list of expressions, representing the conservation law we are analysing
        
        Returns:
            - a boolean variable, it's true is p is a second type conservation law, false otherwise
    '''
    dpt=0
    for i in range(len(indlist)):
        dpt=dpt+mydifftotal(p[i],indlist[i])
    if dpt==0:    
        return true
    return false

def filter(p_list):
    '''
     It filters input laws from all the trivial ones, and retuns filtered laws.
         
  
         Args:
             - p_list: list of expressions lists, representing polynomial conservation laws
      
         Returns:
             - filtered_list: list of expressions lists, representing the polynomial conservation laws taken as input, 
                              without trivial laws
    '''
    start_filter_time = time.time()
    filtered_list=[]
    for p in p_list:
        if not firstKind_check(p) and not secondKind_check(p) :
            filtered_list.append(p)
    return filtered_list


#-----------support functions-----------------------

from collections.abc import Iterable
def initvar(indepX,dependU,listutau):  #declares variables and derivatives
    '''
    It initializes the global variables 'indlist', 'ulist', 'utaulist' with the first, the second 
    and the third argument respectively taken in input.
    
        Args:
            - indepX: string, containing independent variables 
            - dependU: string, containing dependent variables
            - listutau: string, containing derivates
    '''
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

    
def initSigma(Sigma): 
    '''
     It initializes the global variable 'sigma' with the system taken as input, and the global lists: 'principalDer',
         'parametricDer', identifying the principal and parametric derivatives of the system we are analyzing
         
  
         Args:
             - Sigma: dictionary object, representing the system we are analyzing

    '''
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
    '''
    It checks if the 2D-law taken as input is a combination of some of the laws taken as 2nd argument.
    
        Args:
            - D: expression, representing the density of the conservation law to be examined
            - F: expression, representing the flux of the conservation law to be examined
            - Base: list of expressions lists, representing a set of conservation laws
                
        Returns:
            - a boolean variable, true if [D,F] is a combination of some of the laws in Base,
              false, otherwise
    '''
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
    return res 

def computeSout(pt,ptder): 
    '''
    It applies normal form function to an external polynomial.
    
        Args:
            - pt: expression, representing the polynomial to normalize
            - ptder: list of symbols, representing the principl derivatives of pt
            
        Returns:
            - the normalized polynomial
    '''
    completeSigma(ptder)
    reduceSigma()
    return pt.subs({q:sigma[q] for q in ptder}) 


def normalizeLaw(law): 
    '''
    It eliminates parametric derivatives from all the components of the conservation law in question,
    applying the normal form function to each of them.
    
        Args:
            - law: list of expressions, representing the conservation law to be normalized
                
        Returns:
            - a list of expressions representing 'law' in normal form
            
    '''
    res=[]
    for el in law:
        if type(el)==int:
            res.append(el)
        else:
            ptder=list(el.free_symbols.intersection(set(principalDer)))
            res.append(computeSout(el, ptder))
    return res




def div(p):
    '''
    It computes the divergence related to the conservation law taken as input.
    
        Args: 
            - p: list of expressions, representing the law whose divergence is to be calculated.
            
        Returns:
            - an expression which is the divergence associated to law
  
    '''
    return sum([mydifftotal(p[i],indlist[i]) for i in range(len(p))])   
      
def equivalence(L): 
    '''
    It identifies the equivalent laws among those taken as input.
    
        Args: 
            - L: list of expressions lists, representing a set of conservation laws
        
        Returns:
            - equivalence classes of conservation laws (zero=trivial law)
    
    '''
    l=len(L)
    zero=var('zero')
    parlist = list(var('law%d' % j) for j in range(l))
    dpt=sum([parlist[j]*div(L[j]) for j in range(l)])
    gl= list(set(indlist+parametricDer+principalDer))
    cf=Poly(dpt,gl).coeffs()
    equiv=[]
    for bb in parlist:
        s=solve(cf+[bb-1])
        if s!=[]:
            sols={cc for cc in s.keys() if s[cc]!=0}
            if len(sols)==1:
                sols=sols.union({zero})
            equiv.append(sols)
    return eqrel(equiv,parlist)
         


def update(varlist):
    for var in varlist:
        if isPrincipal(var):
            principalDer.append(var)
        else:
            parametricDer.append(var)
            
from itertools import combinations
def eqrel(subsets,wholeset):            
    sets = [set(x) for x in subsets]
    stable = False
    while not stable:                        # loop until no further reduction is found
        stable = True
        # iterate over pairs of distinct sets
        for s,t in combinations(sets, 2):
            if s & t:                        # do the sets intersect ?
                s |= t                       # move items from t to s 
                t ^= t                       # empty t
                stable = False
    # remove empty sets
        sets = [s for s in sets if s!=set()]#list(filter(None, sets)) # added list() for python 3    
    flatset=set(flatten(sets))   # add singletons from wholeset
    for x in wholeset:
        if x not in flatset:
            sets.append(set({x}))
    return sets
        
  
#----------------------------------------------------------------------
#----------------------------Experiments--------------------------------
#----------------------------------------------------------------------
#Experiments are made using five classic PDEs of Mathematical physics: Korteweg-de Vries,
#Boussinesq, Drinfel'd-Sokolv-Wilson, sine-Gordon and 3+1)D Euler's incompressible fluid equations.

'''

#------------Korteweg-de Vries

print('EXAMPLE: Korteweg-de Vries \t')
initvar('t x','u','u00 u10 u01 u03 u02 u04')  
deVries={u10:-u00*u01-u03}   # set alfa=1
initSigma(deVries)

#Anstaz1
print('---Ansatz1: \t')
con_deVries=findConservationLaws([u00, u01, u02, u03],2) #finds conservation laws
filtered_laws=filter(con_deVries) #filters trivial laws
qt=normalizeLaw([(u00**3+3*u00*u02)/6, u01*u10/2+u00**2*u02/2+u00**4/8+u02**2/2-u00*u11/2 ])  #normalizes the law taken as input
checkLinDep(qt[0], qt[1], con_deVries) 
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries) #check if the first law is a linear combination of some of the ACons laws 
checkLinDep(u00, u00**2/2+u02, con_deVries)
print('law\'s number:',len(filtered_laws)) #laws number
equivalence(filtered_laws)

#Anstaz2
print('---Ansatz2: \t')
con_deVries=findConservationLaws([t,x, u00, u01, u02, u03],2)
filtered_laws=filter(con_deVries) 
qt=normalizeLaw([(u00**3+3*u00*u02)/6, u01*u10/2+u00**2*u02/2+u00**4/8+u02**2/2-u00*u11/2]) #no
checkLinDep(qt[0], qt[1], con_deVries)
checkLinDep(-u00**2*t/2+u00*x,(-2*u00**3-6*u00*u02+3*u01**2)*t/6+u00**2*x/2+u02*x-u01, con_deVries)
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries)
checkLinDep(u00, u00**2/2+u02, con_deVries)
print('law\'s number:',len(filtered_laws))

#Anstaz3
print('---Ansatz3: \t')
con_deVries=findConservationLaws([t,x, u00, u01, u02, u03,u04],2)
filtered_laws=filter(con_deVries) 
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
boussinesq={u10:-v01, v10:-u01+3*u00*u01+u03 }   # set beta=1
initSigma(boussinesq)

#Anstaz1
print('---Ansatz1: \t')
con_bouss=findConservationLaws([u00,u01,u02,v00, v01],2)
filtered_laws=filter(con_bouss)
checkLinDep( u00,v00,con_bouss)
checkLinDep( v00, -3*u00**2/2+u00-u02, con_bouss)
qt=normalizeLaw([-u00**3/2+u00**2/2-u02*u00/2+v00**2/2,-3*u00**2*v00/2+(2*v00+u11)*u00/2-v00*u02-u01*u10/2 ])#no
checkLinDep(qt[0], qt[1], con_bouss)
print(qt[0])
print(qt[1])
checkLinDep(u00*v00, -u00**3+v00**2/2+u00**2/2-u02*u00+u01**2/2,con_bouss)
print('law\'s number:',len(filtered_laws))

#Anstaz2
print('---Ansatz2: \t')
con_bouss=findConservationLaws([t,x,u00,u01,u02,u03,v00, v01],2)
filtered_laws=filter(con_bouss)
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
print('---Ansatz3: \t')
con_bouss=findConservationLaws([t,x,u00,u01,u02,u03,u04,v00, v01,v02],2)
filtered_laws=filter(con_bouss)

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
dsw={u10:-3*v00*v01, v10:-2*u00*v01-u01*v00-2*v03 }   # set alfa=1
initSigma(dsw)

#Anstaz1
print('---Ansatz1: \t')
con_dsw=findConservationLaws([u00, u01, v00, v01,v02],2)
filtered_laws=filter(con_dsw) 
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
print('law\'s number:',len(filtered_laws))


#Anstaz2
print('---Ansatz2: \t')
con_dsw=findConservationLaws([t,x,u00, u01,v00, v01,v02,v03],2)
filtered_laws=filter(con_dsw) 
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
checkLinDep(-3*v00**2*t/2+u00*x, (-6*u00*t+3*x)*v00**2/2-6*v00*t*v02+3*v01**2*t,con_dsw)
print('law\'s number:',len(filtered_laws))


#Anstaz3
print('---Ansatz3: \t')
con_dsw=findConservationLaws([t,x,u00, u01,u02,v00, v01,v02,v03,v04],2)
filtered_laws=filter(con_dsw) 
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
checkLinDep(-3*v00**2*t/2+u00*x, (-6*u00*t+3*x)*v00**2/2-6*v00*t*v02+3*v01**2*t,con_dsw)
qt=normalizeLaw([2*u00**3/3+(-18*v00**2+3*u02)*u00/6-9*v02*v00/2, -9*v00**4/4-3*u00**2*v00**2+(-48*u00*v02+12*v01*u01+18*v11)*v00/4+(-12*v01**2-2*u11)*u00/4+u01*u10/2-9*v01*v10/2-9*v02**2 ])
checkLinDep(qt[0], qt[1], con_dsw)
print('law\'s number:',len(filtered_laws))



#------------sine-Gordon

print('EXAMPLE: sine-Gordon \t')
initvar('t x','u v s c','u00 u10 u01 u02 v01 v10 v00 v02 u03 v03 c01 s01 c10 s10 c00 s00')  
gordon={u10:-v00, v10:-u02-s00, s10:c00*u10, c10:-s00*u10, s01:c00*u01, c01:-s00*u01}   # set alfa=1
initSigma(gordon)

#Anstaz1
print('---Ansatz1: \t')
con_sg=findConservationLaws([u00, u01,v00,c00],4)
filtered_laws=filter(con_sg) 
print('law\'s number:',len(filtered_laws))


#Anstaz2
print('---Ansatz2: \t')
con_sg=findConservationLaws([u00, u01,u02,v00,v01,c00],4)
filtered_laws=filter(con_sg) 
qt=normalizeLaw([v00**2/2+u01**2/2+c00,-u10*u01])
checkLinDep(qt[0], qt[1], con_sg)
qt=normalizeLaw([-(v10+u00)*v01, -c00+v00*v10*t+u00*v10+u01**2/2])
checkLinDep(qt[0], qt[1], con_sg)
print('law\'s number:',len(filtered_laws))


#Anstaz3
print('---Ansatz3: \t')
con_sg=findConservationLaws([t,x,u00, u01,u02, v00,v01,c00],4)
filtered_laws=filter(con_sg) 
#qt=normalizeLaw([-(v00*t+u00)*v01, -c00+v00*v10*t+u00*v10+u01**2/2])
#print(checkLinDep(qt[0], qt[1], con_sg))
print('law\'s number:',len(filtered_laws))



#---- (3+1)D Euler's incompressible fluid equations ------

print('EXAMPLE: (3+1)D Euler\'s incompressible fluid equations \t')
initvar('t x y z','u v w p','u0000 u1000 u0100 u0010 u0001 v0000 v1000 v0100 v0010 v0001 w0000 w1000 w0100 w0010 w0001 p0000 p1000 p0100 p0010 p0001')  
Euler={u1000:-(u0000*u0100 + v0000*u0010+ w0000*u0001+p0100),
            v1000:-(u0000*v0100 + v0000*v0010+ w0000*v0001+p0010),
            w1000:-(u0000*w0100 + v0000*w0010+ w0000*w0001+p0001),
            u0100:-(v0010+w0001)}   
initSigma(Euler)

#Anstaz1
con_Euler=findConservationLaws([u0000,v0000,w0000,p0000],2)
filtered_laws=filter(con_Euler)
print('---Ansatz1: \t')
print('law\'s number:',len(filtered_laws))

#Anstaz2
con_Euler=findConservationLaws([t,x,y,z,u0000,v0000,w0000,p0000],2)
filtered_laws=filter(con_Euler)
print('---Ansatz2: \t')
print('law\'s number:',len(filtered_laws))


#---------------other tests

initvar('t x','u','u00 u10 u01 u03 u02 u04')  
deVries={u10:-u00*u01-u03}   # set alfa=1
initSigma(deVries)
con_deVries=findConservationLaws([u00, u01, u02, u03],2)
filtered_laws=filter(con_deVries) 
qt=normalizeLaw([u00*(5*u00**3+40*u00*u02+20*u01**2+36*u04)/120, u00**5/30+u02*u00**3/6+(15*u01**2-20*u11)*u00**2/60+((20*u01*36*u04)*u01+12*u02**2-18*u13)*u00/60-u01**2*u02/10+3*u12*u01/10-3*u02*u11/10+3*u03*(u10+u03)/10])
checkLinDep(qt[0], qt[1], con_deVries)
checkLinDep(u00**2/2, u00**3/3+u00*u02-u01**2/2, con_deVries)
checkLinDep(u00, u00**2/2+u02, con_deVries)
print('law\'s number:',len(filtered_laws))


initvar('t x','u v','u00 u04 u10 u01 u03 u02 v01 v10 v02 v00')  
boussinesq={u10:-v01, v10:-u01+3*u00*u01+u03 }   # set beta=1
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
dsw={u10:-3*v00*v01, v10:-2*u00*v01-u01*v00-2*v03 }   # set alfa=1
initSigma(dsw)
con_dsw=findConservationLaws([u00, u01,v00, v01,v02,v03],2)
filtered_laws=filter(con_dsw) 
checkLinDep(u00, 3*v00**2/2,con_dsw)
checkLinDep(v00**2/2,u00*v00**2+2*v02*v00-v01**2,con_dsw)
qt=normalizeLaw([2*u00**3/3+(-18*v00**2+3*u02)*u00/6-9*v02*v00/2, -9*v00**4/4-3*u00**2*v00**2+(-48*u00*v02+12*v01*u01+18*v11)*v00/4+(-12*v01**2-2*u11)*u00/4+u01*u10/2-9*v01*v10/2-9*v02**2 ])
checkLinDep(qt[0], qt[1], con_dsw)
print('law\'s number:',len(filtered_laws))


initvar('t x','u v s c','u00 u10 u01 u02 v01 v10 v00 v02 u03 v03 c01 s01 c10 s10 c00 s00')  
gordon={u10:-v00, v10:-u02-s00, s10:c00*u10, c10:-s00*u10, s01:c00*u01, c01:-s00*u01}   # set alfa=1
initSigma(gordon)
con_sg=findConservationLaws([u00, u01,v00,c00],2)
filtered_laws=filter(con_sg) 
print('law\'s number:',len(filtered_laws))
 

#-------------- Comparison with Poole & Hereman, JSC 2011 ----------------
#-------------------------------------------------------------------------
#------------------------ (2+1)D equations -------------------------------
#-------------------------------------------------------------------------

#-------ZK

print('EXAMPLE: (2+1)D ZK equation \t')

initvar('t x y','u','u000, u100, u010, u030,u012, u011, u020 ')  
zk={ u100:-u000*u010-u030-u012}   # set alfa=beta=1
initSigma(zk)

#rho terms -> done
#fluxes terms
u001,u020,u011=symbols('u001,u020,u011')
update([u001,u020,u011])
qt=normalizeLaw([3*u000**2, 2*u000**3-3*u001**2-3*u010**2+6*u000*u020, 6*u000*u011])

print('No indipendent variables in the ansatz \t')
con_kz=findConservationLaws([u000,u001,u020,u010,u011],3)
filtered_laws_kza=filter(con_kz) 
print('law\'s number:',len(filtered_laws_kza))
equivalence(filtered_laws_kza) # 2 equivalence classes

print('Hereman comparison\t')
filtered_laws_kza.append(qt)
equivalence(filtered_laws_kza) # 2 equivalence classes, qt in the same class with previuosly found law



#--------

print('With indipendent variables in the ansatz\t')
initvar('t x y','u','u000, u100, u010, u030,u012,u020,u002')  
zk={ u100:-u000*u010-u030-u012}   # set alfa=beta=1
initSigma(zk)

#rho terms -> u010, u001, u020, u002
#fluxes terms
qt=normalizeLaw([y**2*u000, 1/2*y**2*u000**2+y**2*u002+y**2*u020,0])

con_kz=findConservationLaws([t,x,y,u000, u001,u010,u002,u020],4)
filtered_laws_kzb=filter(con_kz) 
print('law\'s number:',len(filtered_laws_kzb))
equivalence(filtered_laws_kzb)  # 111 equivalence classes

print('Hereman comparison\t')
filtered_laws_kzb.append(qt)
equivalence(filtered_laws_kzb) # 111 equivalence classes, qt in the same class with previuosly found law


#-----Gardner

print('EXAMPLE: (2+1)D Gardner equation \t')
initvar('t x y','u v','u000, v000, v010, u010, v001, v011, u020, u100, u001, u030, v002, v020')
gd={u001:v010, v001: u100/3 - u030/3 - 2*u000*u010 + u010*v000 + u000**2*u010/2}
initSigma(gd)

#rho terms-> u_x
#fluxes terms
qt1= normalizeLaw([-u000**2,
  -(3*u000**4)/4 + 4*u000**3 - 3*u000**2*v000 + 2*u000*u020 - u010**2 - 3*v000**2,
  u000**3 + 6*u000*v000])
qt2= normalizeLaw( [-u000/3,
  -(u000**3)/6 +  u000**2 -  u000*v000 +  u020/3,
  (u000**2)/2 +  v000])

print('No indipendent variables in the ansatz\t')
con_gd=findConservationLaws([u000, v000, u010, u020],4) #added 2
filtered_laws_gda=filter(con_gd)
print('law\'s number:',len(filtered_laws_gda))
equivalence(filtered_laws_gda)  # 3 equivalence classes

print('Comparison with Poole & Hereman\t')    
filtered_laws_gda.append(qt1)
filtered_laws_gda.append(qt2)
equivalence(filtered_laws_gda)  #  3 equivalence classes, qt1 and qt2 in the same class with previously found laws, hence non independent 


#-------KP

print('EXAMPLE: (2+1)D KP equation \t')
initvar('t x y','u v','u000 v001 v000 v010 u100 u001 u200 u300 u002 u020 u010 u012 u011 u110 u111 u020 u040 u003 u030')  
kp={u001:v000, v001:-u110-u010**2-u000*u020-u040}
initSigma(kp)

#rho term u_x
#fluxes terms
qt=normalizeLaw([u010,u000*u010+u030,u001])

print('Without indipendent variables in the ansatz \t')
con_kp=findConservationLaws([u000, u010, u030, v000],2)
filtered_laws_kpa=filter(con_kp) 
print('law\'s number:',len(filtered_laws_kpa))
equivalence(filtered_laws_kpa) # 3 equivalence classes

print('Hereman comparison\t')
filtered_laws_kpa.append(qt)
equivalence(filtered_laws_kpa) # 3 equivalence classes, qt in the same class with previuosly found law
'''



