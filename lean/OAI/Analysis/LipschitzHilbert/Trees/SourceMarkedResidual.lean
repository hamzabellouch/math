import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalFullResidual

namespace OAI

/-! The full residual square controls every marked prefix chosen later
by the spatial mass stopping rule. No choice of marks costs a factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem marked_prefix_square_le {E : Type*} [NormedAddCommGroup E]
    (residual : ℕ → E) (count finish : ℕ) (hfinish : finish ≤ count)
    (marked : ℕ → Prop) {B : ℝ}
    (hfull : (∑ j : Fin count, ‖residual j.val‖^2) ≤ B) :
    (∑ j ∈ (Finset.range finish).filter marked, ‖residual j‖^2) ≤ B := by
  classical
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset marked _).trans (Finset.range_mono hfinish))
    (fun j _ _ => sq_nonneg ‖residual j‖))
  rw [← Fin.sum_univ_eq_sum_range (fun j => ‖residual j‖^2) count]
  exact hfull

end LipschitzHilbert

end

end OAI
