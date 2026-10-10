import OAI.Combinatorics.PolynomialVacuum.Puncture.CorrectionGram
import OAI.Combinatorics.PolynomialVacuum.Puncture.Simultaneous
import OAI.Combinatorics.PolynomialVacuum.Puncture.GramAlgebra

namespace OAI

namespace PolynomialVacuumCylinder
open Real Matrix MeasureTheory

 

theorem denominator_gram_log_comparison : DenominatorGramLogComparison := by
  intro n hn
  obtain ⟨V,d,hV,hd,hVA,hVB⟩ := positive_gram_simultaneous
    (denominatorReferenceMatrix n) (denominatorMomentMatrix n)
    (denominatorReferenceMatrix_posDef n) (denominatorMomentMatrix_posDef n)
  have hj (i : Fin n) : (star V*denominatorCorrectionMatrix n*V) i i≤Real.log (d i) := by
    have h := denominator_scalar_jensen (V.col i) (isUnit_col_ne_zero V hV i)
    rw [←denominator_correction_gram_identity,
      ←denominator_reference_gram_identity,←denominator_gram_identity] at h
    simp only [←conjugate_diagonal_gram,hVA,hVB,Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq,div_one] at h
    exact h
  have ht : (star V*denominatorCorrectionMatrix n*V).trace≤∑ i,Real.log (d i) :=
    Finset.sum_le_sum fun i _=>hj i
  rw [normalized_gram_trace _ _ _ hV hVA] at ht
  rw [←normalized_gram_logdet (denominatorReferenceMatrix n) (denominatorMomentMatrix n)
    V d (denominatorReferenceMatrix_det_pos n) (denominatorMomentMatrix_det_pos n) hd hVA hVB] at ht
  exact ht

end PolynomialVacuumCylinder

end OAI
