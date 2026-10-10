import OAI.Combinatorics.PolynomialVacuum.Separator.NormalFamily
import OAI.Combinatorics.PolynomialVacuum.Pairing.PairingMain

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumAlgebra MeasureTheory

 

noncomputable def homogeneousEmpty (N : ℕ) : ℂ :=
  emptyCoefficient polynomialVacuum N

noncomputable def punctureD0 : ℝ := 2+Real.sqrt 2

 

def HomogeneousDenominatorBound : Prop :=
  ∃ c : ℝ, 0<c ∧ ∀ n : ℕ, 1≤n →
    (homogeneousEmpty (2*n)).im=0 ∧
    c * punctureD0^(-(n : ℤ)) * (4*punctureD0^2/9)^(n^2) * (n : ℝ)^(5/48 : ℝ)
      ≤ (homogeneousEmpty (2*n)).re

 

noncomputable def denominatorMomentWeight (p : ℝ) : ℝ :=
  if p=0 then 1/Real.pi
  else p*Real.cosh (Real.pi*p/8)/(2*Real.sinh (Real.pi*p/2))

noncomputable def denominatorMomentMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k=>∫ p : ℝ,p^(2*j.val+2*k.val)*denominatorMomentWeight p

 

def HomogeneousMomentIdentity : Prop := ∀ n : ℕ, 1≤n →
  homogeneousEmpty (2*n)=
    ((((punctureD0/2)^((2*n).choose 2) * (denominatorMomentMatrix n).det /
       (∏ j∈Finset.range (2*n), (j.factorial : ℝ))) : ℝ) : ℂ)

end PolynomialVacuumCylinder

end OAI
