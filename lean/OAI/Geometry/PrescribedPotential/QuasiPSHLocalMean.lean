import Mathlib
import OAI.Geometry.PrescribedPotential.BallSubmean
import OAI.Geometry.PrescribedPotential.QuadraticContact

namespace OAI

/-! Quasi P S H Local Mean. -/

section

 

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace
namespace PotentialABP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
local instance quasiPSHLocalMeanRealInnerProductSpace : InnerProductSpace ℝ E :=
  InnerProductSpace.rclikeToReal ℂ E

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
lemma closedBall_small_center_subset {c y : E} {r : ℝ} (hy : y ∈ ball c r) :
    closedBall y (2*r) ⊆ closedBall c (3*r) := by
  intro x hx
  have ht := dist_triangle x y c
  have hy' : dist y c < r := hy
  have hx' : dist x y ≤ 2*r := hx
  change dist x c ≤ 3*r
  linarith

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
lemma ball_small_center_subset {c y : E} {r : ℝ} (hy : y ∈ ball c r) :
    ball c r ⊆ ball y (2*r) := by
  intro x hx
  have ht := dist_triangle x c y
  have hy' : dist c y < r := by simpa [dist_comm] using hy
  have hx' : dist x c < r := hx
  change dist x y < 2*r
  linarith

 

theorem quasiPSH_local_integral
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (c : E) {r C M : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hupper : ∀ x ∈ closedBall c (3*r), f x ≤ M)
    (hlevi : ∀ x ∈ closedBall c (3*r), ∀ v : E,
      -(4*C*‖v‖^2) ≤ fderiv ℝ (fderiv ℝ f) x v v +
        fderiv ℝ (fderiv ℝ f) x (Complex.I • v) (Complex.I • v))
    {y : E} (hy : y ∈ ball c r) :
    (∫ x in ball c r, M-f x) ≤
      volume.real (ball (0:E) (2*r)) * (M-f y+9*C*r^2) := by
  let q : E → ℝ := fun x => C*‖x-c‖^2
  have hq : ContDiff ℝ ∞ q := contDiff_const.mul
    ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hsub := closedBall_small_center_subset hy
  have hmean := smooth_ball_submean (hf.add hq) y (by positivity : 0 ≤ 2*r) ?_
  · have hu : IntegrableOn (fun x => M-f x) (ball y (2*r)) :=
      ((continuous_const.sub hf.continuous).continuousOn.integrableOn_compact
        (isCompact_closedBall y (2*r))).mono_set ball_subset_closedBall
    have hfi : IntegrableOn f (ball y (2*r)) :=
      (hf.continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall y (2*r))).mono_set ball_subset_closedBall
    have hqi : IntegrableOn q (ball y (2*r)) :=
      (hq.continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall y (2*r))).mono_set ball_subset_closedBall
    have hvol : volume.real (ball y (2*r)) = volume.real (ball (0:E) (2*r)) := by
      simpa only [setIntegral_const, smul_eq_mul, mul_one] using
        (ball_integral_translate (fun _ : E => (1:ℝ)) y (2*r)).symm
    have hqB : (∫ x in ball y (2*r), q x) ≤
        volume.real (ball (0:E) (2*r)) * (9*C*r^2) := by
      have hm : (∫ x in ball y (2*r), q x) ≤
          ∫ _x in ball y (2*r), (9*C*r^2) := by
        apply setIntegral_mono_on hqi (integrableOn_const (C := (9*C*r^2)))
          isOpen_ball.measurableSet
        intro x hx
        have hb := hsub (ball_subset_closedBall hx)
        have hn : ‖x-c‖ ≤ 3*r := by simpa [mem_closedBall, dist_eq_norm] using hb
        have hs := (sq_le_sq₀ (norm_nonneg (x-c)) (by positivity : 0 ≤ 3*r)).mpr hn
        change C*‖x-c‖^2 ≤ 9*C*r^2
        nlinarith [mul_le_mul_of_nonneg_left hs hC]
      simpa only [setIntegral_const, smul_eq_mul, hvol] using hm
    have hm : (∫ x in ball c r, M-f x) ≤ ∫ x in ball y (2*r), M-f x := by
      apply setIntegral_mono_set hu _ (Filter.Eventually.of_forall (ball_small_center_subset hy))
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
      exact sub_nonneg.mpr (hupper x (hsub (ball_subset_closedBall hx)))
    have hic : IntegrableOn (fun _ : E => M) (ball y (2*r)) volume :=
      integrableOn_const (C := M)
    apply hm.trans
    rw [integral_sub hic hfi,
      setIntegral_const, smul_eq_mul, hvol]
    rw [integral_add hfi hqi] at hmean
    have hq0 : 0 ≤ q y := mul_nonneg hC (sq_nonneg _)
    have hV : 0 ≤ volume.real (ball (0:E) (2*r)) := ENNReal.toReal_nonneg
    nlinarith [mul_nonneg hV hq0]
  · intro x hx v
    have h := hlevi x (hsub hx) v
    change 0 ≤ fderiv ℝ (fderiv ℝ (fun x => f x + C*‖x-c‖^2)) x v v +
      fderiv ℝ (fderiv ℝ (fun x => f x + C*‖x-c‖^2)) x (Complex.I • v) (Complex.I • v)
    rw [quadratic_add_hessian hf, quadratic_add_hessian hf]
    simp only [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
    linarith

end PotentialABP

end
end

end OAI
