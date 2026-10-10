import OAI.Combinatorics.PolynomialVacuum.Puncture.Moments

namespace OAI

namespace PolynomialVacuumCylinder
open MeasureTheory

 
noncomputable def denominatorReferenceMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k=>∫ p : ℝ,p^(2*j.val+2*k.val)*denominatorReferenceWeight p

 

noncomputable def denominatorCorrectionMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k=>∫ p : ℝ,p^(2*j.val+2*k.val)*
    denominatorReferenceWeight p*denominatorCorrection p

 

noncomputable def denominatorCorrectionTrace (n : ℕ) : ℝ :=
  ((denominatorReferenceMatrix n)⁻¹*denominatorCorrectionMatrix n).trace

 

def SharpReferenceTraceBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1≤n →
    (5/48 : ℝ)*Real.log (n : ℝ)-C ≤ denominatorCorrectionTrace n

 

def ReferenceDeterminantEvaluation : Prop := ∀ n : ℕ,
  (punctureD0/2)^((2*n).choose 2)*(denominatorReferenceMatrix n).det /
    (∏ j∈Finset.range (2*n),(j.factorial : ℝ)) =
      punctureD0^(-(n : ℤ))*(4*punctureD0^2/9)^(n^2)

 

def DenominatorGramLogComparison : Prop := ∀ n : ℕ, 1≤n →
  denominatorCorrectionTrace n ≤
    Real.log (denominatorMomentMatrix n).det-Real.log (denominatorReferenceMatrix n).det

end PolynomialVacuumCylinder

end OAI
