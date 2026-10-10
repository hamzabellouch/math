import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RationalComplexMatrix

namespace OAI

/-! The exact K=34 recipe of the manuscript, Appendix `cert:profile`.
All operations here are rational. Its analytic interpretation is established
separately; no certificate comparison is assumed. -/

namespace DefocusingNLS.ProfileCertificate

abbrev QMatrix := Matrix2 RationalComplex
abbrev RMatrix := Matrix2 ℚ

def centerB : ℚ := 33477606871236 / 100000000000000
def centerZ : ℚ := 270506819293654 / 100000000000000
def radius : ℚ := 1 / 100000000

def parameterB : QMatrix := ⟨⟨0,-1⟩,0,⟨0,-1⟩,⟨0,-1⟩⟩
def parameterZ : QMatrix := ⟨⟨0,-1⟩,⟨0,-1⟩,0,0⟩
def majorant : RMatrix :=
  Matrix2.add (Matrix2.map RationalComplex.absOne parameterB)
    (Matrix2.map RationalComplex.absOne parameterZ)

def factor (n : ℕ) : QMatrix :=
  ⟨⟨(n : ℚ)-5, -centerB-centerZ⟩, ⟨0,-centerZ⟩,
   ⟨(n : ℚ),-centerB⟩, ⟨(n : ℚ),-centerB⟩⟩

structure State where
  value : QMatrix
  derivB : QMatrix
  derivZ : QMatrix
  error : RMatrix
  deriving DecidableEq

def initial : State := ⟨Matrix2.one, Matrix2.zero, Matrix2.zero, Matrix2.zero⟩

/-- All four right-hand sides use the old state, as in the supplement. -/
def step (n : ℕ) (s : State) : State :=
  let inv : RationalComplex := ⟨((n : ℚ)+1)⁻¹,0⟩
  { value := Matrix2.scale inv (Matrix2.mul (factor n) s.value)
    derivB := Matrix2.scale inv (Matrix2.add (Matrix2.mul parameterB s.value)
      (Matrix2.mul (factor n) s.derivB))
    derivZ := Matrix2.scale inv (Matrix2.add (Matrix2.mul parameterZ s.value)
      (Matrix2.mul (factor n) s.derivZ))
    error := Matrix2.scale (((n : ℚ)+1)⁻¹)
      (Matrix2.add
        (Matrix2.mul (Matrix2.add (Matrix2.map RationalComplex.absOne (factor n))
          (Matrix2.scale radius majorant)) s.error)
        (Matrix2.mul majorant (Matrix2.add
          (Matrix2.map RationalComplex.absOne s.derivB)
          (Matrix2.map RationalComplex.absOne s.derivZ)))) }

/-- Descending multiplication of factors 33 through 0. -/
def result : State := (List.range 34).foldr step initial

def normalized (z : RationalComplex) : RationalComplex :=
  RationalComplex.quotient z result.value.b

def changeBound : ℚ := 40*radius + 50000*radius^2

def denominatorGap : ℚ :=
  234/100 - (318/100)*centerZ/5 -
    ((1+(centerZ+radius)/5)*changeBound+(318/100)*radius/5) -
    ((centerZ+radius)/5*changeBound+(318/100)*radius/5)

def jetError : ℚ :=
  (1/1000000000000+50000*radius^2+(283/1000)*radius*changeBound)/(1-changeBound)

def tailError : ℚ :=
  (2*(centerZ+radius)/5)*(62/10000000000000)/((6/10)*(1-changeBound))

end DefocusingNLS.ProfileCertificate

end OAI
