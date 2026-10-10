import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusArc

namespace OAI

/-! A cubic remainder estimate at a scalar flat second jet. This is the
low-dimensional flat-stratum estimate needed for double-locus regularity. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance scalarFirstNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance scalarFirstSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
local instance scalarSecondNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance scalarSecondSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance scalarThirdNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance scalarThirdSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance

lemma scalar_flat_cubic_bound {f : Base → ℝ} (hf : ContDiff ℝ ∞ f)
    (x y : Base) (hfirst : fderiv ℝ f x = 0)
    (hsecond : fderiv ℝ (fderiv ℝ f) x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hthird : ∀ z ∈ closedBall x ‖y-x‖,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ M) :
    ‖f y-f x‖ ≤ M*‖y-x‖^3 := by
  let d := ‖y-x‖
  have hd : 0 ≤ d := norm_nonneg _
  let B := closedBall x d
  have hx : x ∈ B := mem_closedBall_self hd
  have hy : y ∈ B := by simp only [B,d,mem_closedBall,dist_eq_norm,le_refl]
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hDD := hD.fderiv_right (m := ∞) (by simp)
  have hsecond_bound (z : Base) (hz : z ∈ B) :
      ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M*d := by
    have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hDD.differentiable (by simp) w) hthird hx hz
    rw [hsecond,sub_zero] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) hM
  have hfirst_bound (z : Base) (hz : z ∈ B) : ‖fderiv ℝ f z‖ ≤ (M*d)*d := by
    have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hD.differentiable (by simp) w) hsecond_bound hx hz
    rw [hfirst,sub_zero] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) (mul_nonneg hM hd)
  have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hf.differentiable (by simp) w) hfirst_bound hx hy
  calc
    _ ≤ (M*d*d)*‖y-x‖ := h
    _ = M*‖y-x‖^3 := by dsimp [d]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
