import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.FullSet

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasSecondTaylor_of_second_derivative {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {x : E} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hD : HasFDerivAt f' B x) :
    HasSecondTaylor (fun h => f (x+h)) (f' x) B := by
  have hs : ∀ v w, B v w=B w v := second_derivative_symmetric_of_eventually hf hD
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD).def hε
  have hnear : ∀ᶠ h : E in 𝓝 0, HasFDerivAt f (f' (x+h)) (x+h) := by
    exact (show ContinuousAt (fun h : E => x+h) 0 from continuousAt_const.add continuousAt_id).eventually
      (by simpa only [add_zero] using hf)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hnear.and hrem)
  let R : E → ℝ := fun h => f (x+h)-f x-f' x h-B h h/2
  have hR0 : R 0=0 := by simp [R]
  have hdR : ∀ z ∈ Metric.ball (0:E) r,
      HasFDerivAt R (f' (x+z)-f' x-B z) z := by
    intro z hz
    have hshift : HasFDerivAt (fun h : E => x+h) (ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).const_add x
    have hbase := (hball hz).1.comp (f := fun h : E => x+h) z hshift
    have hquad : HasFDerivAt (fun v : E => B v v/2) (B z) z := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1/2:ℝ)
      have he : (fun v : E => B v v/2)=((1/2:ℝ) • fun v : E => B v v) := by
        ext v; simp only [Pi.smul_apply,smul_eq_mul]; ring
      rw [he]
      apply H.congr_fderiv
      ext v
      simp only [smul_apply,add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v z]
      ring
    convert! ((hbase.sub_const (f x)).sub (f' x).hasFDerivAt).sub hquad using 1
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  have hsub : Metric.closedBall (0:E) ‖h‖ ⊆ Metric.ball (0:E) r := by
    intro z hz
    simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right] at hz hh ⊢
    exact lt_of_le_of_lt hz hh
  have H := (convex_closedBall (0:E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hdR z (hsub hz)).hasFDerivWithinAt)
    (show ∀ z ∈ Metric.closedBall (0:E) ‖h‖, ‖f' (x+z)-f' x-B z‖≤ε*‖h‖ from by
      intro z hz
      exact (hball (hsub hz)).2.trans
        (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hε.le))
    (Metric.mem_closedBall_self (norm_nonneg h))
    (show h ∈ Metric.closedBall (0:E) ‖h‖ by simp)
  simpa only [hR0,sub_zero,R,add_zero,pow_two,Real.norm_eq_abs,abs_pow,
    abs_norm,abs_mul,mul_assoc] using H

end WeakMTWTransport

end

end OAI
