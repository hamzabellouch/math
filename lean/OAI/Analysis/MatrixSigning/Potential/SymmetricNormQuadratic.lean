import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Hilbert
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma symmetric_norm_le_of_quadratic (T : E →L[ℝ] E) (hsym : T.IsSymmetric)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, |inner ℝ (T x) x| ≤ c * ‖x‖^2) : ‖T‖ ≤ c := by
  rw [T.norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hc
  · have hn : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    simp only [RCLike.re_to_real, abs_div, abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (h x)

end
end CurrentKS.Hilbert

end OAI
