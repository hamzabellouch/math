import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.QuotientStable
import OAI.Analysis.Kaplansky.Quotient.TracePullback
import OAI.Analysis.Kaplansky.Quotient.Extraction

namespace OAI

noncomputable section

namespace KaplanskyConsequences


open Kaplansky SpectralKernel
open scoped BigOperators ComplexOrder
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

lemma no_tracialState_of_twoThirds {A : Type*} [CStarAlgebra A] [Nontrivial A] {n : ℕ}
    (y : Fin n → A) (hcol : ∑ i, star (y i)*y i = 1)
    (hrow : ∑ i, y i*star (y i) ≤ (2/3 : ℂ) • (1 : A)) :
    IsEmpty (TracialState A) := by
  apply no_tracialState_of_finite_obstruction y hcol
  have hpos : 0 ≤ ∑ i, y i*star (y i) := Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
  apply lt_of_le_of_lt (CStarAlgebra.norm_le_norm_of_le_of_nonneg hrow hpos)
  calc
    ‖(2/3 : ℂ) • (1 : A)‖ = ‖(2/3 : ℂ)‖ * ‖(1 : A)‖ := norm_smul _ _
    _ ≤ ‖(2/3 : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (le_of_eq (norm_one (α := A))) (norm_nonneg _)
    _ < 1 := by norm_num [Complex.norm_div]

theorem actualAlgebra_no_tracialState : IsEmpty (TracialState ActualAlgebra) := by
  have := actualAlgebra_nontrivial_separable.1
  apply no_tracialState_of_twoThirds (generatedGenerator actualBoundedGenerator)
  · exact actual_test_shift_algebra.2.2.1
  · exact actual_test_shift_algebra.2.2.2

theorem trace_free_stably_finite_exists : TraceFreeStablyFinite := by
  let d : CuntzDimensionState ActualAlgebra := Classical.choice
    (cuntzDimensionState_nonempty fun k hk => actualAlgebra_matrix_not_properlyInfinite hk)
  have := actualAlgebra_nontrivial_separable.1
  exact separable_extraction (faithfulQuotient_stablyFinite d)
    (no_tracialState_of_map (quotientHom d) actualAlgebra_no_tracialState)


end KaplanskyConsequences

end

end OAI
