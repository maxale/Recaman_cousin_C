# In the code below, we use int() instead of lift() since it works well in both cases: integer q and q=None
# lift() fails when its argument is an integer

# return len(W(1,m,b)) based on Lemma 1
def lenW(m,b):
   if m==0:
      return 0
   l = ZZ(m).ndigits(b)
   return l*(m+1) - (b^l - 1)/(b-1)


# return valW(b^(l-1),m,b) modulo q (if given), where b^(l-1) <= m < b^l, based on Lemma 2
def valWblm(m,b,q=None):
   l = ZZ(m).ndigits(b)
   B = b
   D = [(b^l-1)^2, 1]
   if q:
      g = gcd(D[0],q)
      while g>1:
        D[0] //= g
        D[1] *= g
        g = gcd(D[0],g)
      B = Integers(q*D[1])(b)
   return int( (m - (m+1)*B^l + (B^(2*l-1)-B^(l-1)+1)*B^(l*(m+1-b^(l-1))) ) // D[0] ) // D[1]


# return valW(n,m,b) modulo q (if given) based on Lemma 3
def valWnm(n,m,b,q=None):
   l = ZZ(m).ndigits(b)
   B = b
   if q:
      B = Integers(q)(b)
   res = valWblm(m,b,q) + sum( valWblm(b^k-1,b,q) * B^( l*(m+1) - ((b^(l-k)-1)/(b-1)+k)*b^k ) for k in range(1,l) )
   if n>1:
      res -= valWnm(1,n-1,b,q) * B^(lenW(m,b)-lenW(n-1,b))
   return int(res)


# return the value of a_{n,l} in base b and modulo q (if given)
def compute_a(n,l,b=10,q=None):
   B = b
   if q:
      B = Integers(q)(b)
   Bl = B^l
   return int( (valWnm(n,b^l-1,b,q) + 1)*(Bl-1)^2  + Bl )




# auxliary routine to check that (p,m,d) is a solution to (4)
def isSol2(p,m,d,b,n,l,verbose=True):
   if verbose:
      print ("enter isSol2", p,m,d,b,n,l)
   if m % p^d:
      return False
   bl = b^l
   s = valuation(bl-1,p)
   Bl = Integers(p^(d+2*s))(bl)
   return (compute_a(n,l,b,p^(d+2*s))*Bl^(m-bl) - (Bl-1)*m - 1) == 0



# returns C(n) = m-n with L/b < m <= L, or None
# Solve(2,10,2) gives 80
def Solve(n,b,l,verbose=false,tracem=0,tracep=0):
   L = b^l
   assert b % 2 == 0
   assert n < L
   T = [1 for m in range(L+1)]
   for p in prime_range(L+1):
      if verbose or p==tracep:
         print ("p=", p)

      A = compute_a(n,l,b,p)
      #print("A = ",A, [n,l,b,p])
      if verbose or p==tracep:
         print ("A=", A)
      if b % p == 0 or A == 0:
         continue
      Gp = GF(p)
      r1 = Gp(L).multiplicative_order()
      if verbose or p==tracep:
         print ("r1=", r1)
      if r1 > 1:
         if power_mod(A,r1,p) != 1:
            continue
         try:
            q = Gp(A).log(L)
         except ValueError:
            continue
         M = r1*p
         m0 = ((L-q)*p) % M
      else: # case r1=1
         m0 = 0
         if p==2:
            M = 4
         else:
            M = p
      if m0 == 0:
         m0 = M

      d = 1
      if verbose or p==tracep:
         print ("m0=", m0, "M=", M)
      while m0 <= L and isSol2(p,m0,d,b,n,l,verbose):
         if verbose or p==tracep:
            print ("start of loop: m0=", m0)
         # we want m = m0 + k*M with k >= 0 and m >= L/b+1
         m = m0 + ceil((L/b+1-m0)/M)*M
         if verbose or p==tracep:
            print ("p=", p, "m=", m)
         while m <= L:
            T[m] *= p
            if m==tracem or p==tracep:
               print ("p=", p, "m=", m, "T[m]=", T[m])
            m = m+M
         m0 = m0*p
         M = M*p
         d = d+1
      if p==2 and m0//2<=L and isSol2(p,m0//2,d,b,n,l): # case p=2 and d=D
         m0 = m0//2
         m = m0 + ceil((L/b+1-m0)/M)*M
         while m <= L:
            T[m] *= p
            m += M
   # we should have m>=n
   for m in (max(n+2,L//b+1)..L):
      if T[m]==m:
         return m-n-1
   return None


# computes C(n), using Solve() with increasing intervals [b^(l-1),b^l]
# default base is b=10
def A332580a(n,b=10,verbose=false,maxi=infinity):
   # we should have n <= m < b^l
   l = ZZ(n).ndigits(b)
   while True:
      L = b^l
      if verbose:
         print ("searching in", L//b, L)
      res = Solve(n,b,l)
      if res != None:
         return min(res,maxi)
      # the new interval is [b^l,b^(l+1)] thus will give values >= b^l-n
      if b^l-n > maxi:
         return maxi
      l = l+1
