import OAI.Geometry.NodalSets.Elliptic.AmplitudeBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma first_order_remainder_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Coord → E) (y : Coord) (r C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ z, ‖z-y‖ ≤ r → ContDiffAt ℝ ∞ f z)
    (hb : ∀ z, ‖z-y‖ ≤ r → ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
    (x : Coord) (hx : ‖x-y‖ ≤ r) :
    ‖f x-f y-fderiv ℝ f y (x-y)‖ ≤ C*‖x-y‖^2 := by
  let R := ‖x-y‖
  have hR : 0 ≤ R := norm_nonneg _
  have h0 : ‖y-y‖ ≤ r := by simpa using hR.trans hx
  have hd (z : Coord) (hz : ‖z-y‖ ≤ R) :
      ‖fderiv ℝ f z - fderiv ℝ f y‖ ≤ C*‖z-y‖ :=
    norm_sub_le_on_closedBall (fderiv ℝ f) y R C hC
      (fun v hv ↦ ((hs v (hv.trans hx)).fderiv_right (by simp) :
        ContDiffAt ℝ ∞ (fderiv ℝ f) v).differentiableAt (by simp))
      (fun v hv ↦ hb v (hv.trans hx)) hR z hz
  let q : Coord → E := fun z ↦ f z-f y-fderiv ℝ f y (z-y)
  have hq (z : Coord) (hz : ‖z-y‖ ≤ R) :
      HasFDerivAt q (fderiv ℝ f z-fderiv ℝ f y) z := by
    have h := ((hs z (hz.trans hx)).differentiableAt (by simp)).hasFDerivAt
    convert (h.sub_const (f y)).sub ((fderiv ℝ f y).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const y)) using 1 <;> rfl
  have hrem := norm_sub_le_on_closedBall q y R (C*R) (mul_nonneg hC hR)
    (fun z hz ↦ (hq z hz).differentiableAt)
    (fun z hz ↦ by rw [(hq z hz).fderiv]; exact (hd z hz).trans (mul_le_mul_of_nonneg_left hz hC))
    hR x le_rfl
  simpa [q,R,pow_two,mul_assoc] using hrem

end
end Yau.Geometry

end OAI
