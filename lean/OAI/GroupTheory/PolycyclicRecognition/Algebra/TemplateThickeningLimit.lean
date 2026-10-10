import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # Removing the final height-template enlargement -/

namespace PolycyclicRecognition.SupportDatum

open Set Metric
open scoped Pointwise

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B)

/-- An exponent bounded by every positive thickening is bounded by the
original compact template. -/
theorem le_templateSupport_of_thickenings {E : Set W} (hE : IsCompact E)
    (hne : E.Nonempty) {p : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → p ≤ D.templateSupport (E + closedBall 0 ε)) :
    p ≤ D.templateSupport E := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (D.templateSupportConstant + 1)
  have hε : 0 < ε := div_pos hη (by linarith [D.templateSupportConstant_nonneg])
  have hn : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z + 0, add_mem_add hz (by simpa using hε.le)⟩
  have hu := D.templateSupport_le_of_nearby (hE.add (isCompact_closedBall 0 ε)) hn
    hE hε.le (show ∀ x ∈ E + closedBall 0 ε, ∃ y ∈ E, ‖x - y‖ ≤ ε by
      rintro x ⟨y, hy, u, hu, rfl⟩
      refine ⟨y, hy, ?_⟩
      simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using hu)
  have hsmall : D.templateSupportConstant * ε ≤ η := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [D.templateSupportConstant_nonneg])).mpr
    nlinarith
  exact (h ε hε).trans (hu.trans (add_le_add le_rfl hsmall))

end PolycyclicRecognition.SupportDatum

end OAI
