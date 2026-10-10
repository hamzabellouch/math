import Mathlib

namespace OAI

/-! A smooth supported quotient only requires a nonzero denominator on its support. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma supported_quotient_smooth {χ d : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hd : ContDiff ℝ ∞ d)
    (hne : ∀ x ∈ tsupport χ, d x ≠ 0) :
    ContDiff ℝ ∞ (fun x => χ x / d x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.div hd.contDiffAt (hne x hx)
  · have hz : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : (fun y => χ y / d y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hz] with y hy
      rw [hy, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he

omit [NormedSpace ℝ E] in
lemma supported_quotient_support (χ d : E → ℝ) :
    tsupport (fun x => χ x / d x) ⊆ tsupport χ := by
  simpa only [div_eq_mul_inv] using
    (tsupport_mul_subset_left (f := χ) (g := fun x => (d x)⁻¹))

omit [NormedSpace ℝ E] in
lemma supported_quotient_compact {χ d : E → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x / d x) := by
  exact hχ.of_isClosed_subset (isClosed_tsupport _) (supported_quotient_support χ d)

omit [NormedSpace ℝ E] in
lemma supported_quotient_cancel {χ d : E → ℝ}
    (hne : ∀ x ∈ tsupport χ, d x ≠ 0) (x : E) : (χ x / d x) * d x = χ x := by
  by_cases hd : d x = 0
  · have hx : x ∉ tsupport χ := fun h => hne x h hd
    rw [image_eq_zero_of_notMem_tsupport hx, zero_div, zero_mul]
  · exact div_mul_cancel₀ _ hd

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
