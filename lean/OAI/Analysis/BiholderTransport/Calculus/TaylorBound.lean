import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

section TaylorBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_order_remainder_bound_on_ball {f : E → ℝ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε)
    (hf : ∀ z ∈ Metric.ball (0:E) r, ContDiffAt ℝ 2 f z)
    (hB : ∀ z ∈ Metric.ball (0:E) r,
      ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) 0‖ ≤ ε)
    {h : E} (hh : h ∈ Metric.ball (0:E) r) :
    |f h - f 0 - fderiv ℝ f 0 h - fderiv ℝ (fderiv ℝ f) 0 h h / 2| ≤ ε * ‖h‖^2 := by
  let D := fderiv ℝ f 0
  let B := fderiv ℝ (fderiv ℝ f) 0
  let R : E → ℝ := fun z => f z - f 0 - D z - B z z / 2
  let R' : E → E →L[ℝ] ℝ := fun z => fderiv ℝ f z - D - B z
  have h0 : (0:E) ∈ Metric.ball (0:E) r := Metric.mem_ball_self hr
  have hs : ∀ v w, B v w = B w v :=
    fun v w => ((hf 0 h0).isSymmSndFDerivAt (by norm_num)).eq v w
  have hdR' : ∀ z ∈ Metric.ball (0:E) r,
      HasFDerivAt R' (fderiv ℝ (fderiv ℝ f) z - B) z := by
    intro z hz
    exact ((((hf z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.sub_const D).sub B.hasFDerivAt
  have hR' : ∀ z ∈ Metric.ball (0:E) r, ‖R' z‖ ≤ ε * ‖z‖ := by
    intro z hz
    have H := (convex_ball (0:E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hdR' z hz).hasFDerivWithinAt) hB h0 hz
    simpa only [R',D,B,map_zero,sub_self,sub_zero] using H
  have hdR : ∀ z ∈ Metric.ball (0:E) r, HasFDerivAt R (R' z) z := by
    intro z hz
    have hquad : HasFDerivAt (fun v : E => B v v / 2) (B z) z := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1/2:ℝ)
      have he : (fun v : E => B v v / 2) = ((1/2:ℝ) • fun v : E => B v v) := by
        ext v
        simp only [Pi.smul_apply,smul_eq_mul]
        ring
      rw [he]
      apply H.congr_fderiv
      ext v
      simp only [_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v z]
      ring
    exact (((hf z hz).differentiableAt (by norm_num)).hasFDerivAt.sub_const (f 0)
      |>.sub D.hasFDerivAt |>.sub hquad)
  have hsub : Metric.closedBall (0:E) ‖h‖ ⊆ Metric.ball (0:E) r := by
    intro z hz
    simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right] at hz hh ⊢
    exact lt_of_le_of_lt hz hh
  have H := (convex_closedBall (0:E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hdR z (hsub hz)).hasFDerivWithinAt)
    (show ∀ z ∈ Metric.closedBall (0:E) ‖h‖, ‖R' z‖ ≤ ε * ‖h‖ from by
      intro z hz
      apply (hR' z (hsub hz)).trans
      exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hε)
    (Metric.mem_closedBall_self (norm_nonneg h))
    (show h ∈ Metric.closedBall (0:E) ‖h‖ by simp)
  simpa only [R,D,B,map_zero,_root_.zero_apply,zero_div,sub_self,sub_zero,Real.norm_eq_abs,
    pow_two,mul_assoc] using H

end TaylorBound

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [CompactSpace P]

lemma compact_parametric_second_order_remainder
    (f : P → E → ℝ)
    (hf : ∀ a : P, ∀ᶠ q : E × P in 𝓝 (0,a), ContDiffAt ℝ 2 (f q.2) q.1)
    (hD : ∀ a : P, ContinuousAt (fun q : E × P => fderiv ℝ (fderiv ℝ (f q.2)) q.1) (0,a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : E in 𝓝 0, ∀ a : P,
      |f a h - f a 0 - fderiv ℝ (f a) 0 h -
        fderiv ℝ (fderiv ℝ (f a)) 0 h h / 2| ≤ ε * ‖h‖^2 := by
  have hloc : ∀ a ∈ (univ : Set P), ∀ᶠ q : E × P in 𝓝 (0,a),
      ContDiffAt ℝ 2 (f q.2) q.1 ∧
      ‖fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) 0‖ ≤ ε := by
    intro a _
    have hc0 : ContinuousAt (fun q : E × P => ((0:E),q.2)) ((0:E),a) :=
      continuousAt_const.prodMk continuousAt_snd
    have hcB0 : ContinuousAt (fun q : E × P =>
        fderiv ℝ (fderiv ℝ (f q.2)) 0) (0,a) :=
      by
      simpa only [Function.comp_def] using (hD a).comp (x := ((0:E),a)) (f := fun q : E × P => ((0:E),q.2)) hc0
    have hc : ContinuousAt (fun q : E × P =>
        ‖fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) 0‖) (0,a) :=
      by
      have hh : ContinuousAt (fun q : E × P =>
        fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) (0:E)) ((0:E),a) :=
        (hD a).sub hcB0
      exact @ContinuousAt.norm (E × P) (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ hh
    have he : ∀ᶠ q : E × P in 𝓝 (0,a),
        ‖fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) 0‖ < ε :=
      hc.eventually_lt continuousAt_const (by simpa only [sub_self, ContinuousLinearMap.opNorm_zero] using hε)
    exact (hf a).and (he.mono (fun _ h => h.le))
  have he : ∀ᶠ h : E in 𝓝 0, ∀ a ∈ (univ : Set P),
      ContDiffAt ℝ 2 (f a) h ∧
      ‖fderiv ℝ (fderiv ℝ (f a)) h - fderiv ℝ (fderiv ℝ (f a)) 0‖ ≤ ε :=
    isCompact_univ.eventually_forall_of_forall_eventually hloc
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  intro a
  apply second_order_remainder_bound_on_ball hr hε.le
  · intro z hz
    exact (hball (y := z) hz a (mem_univ a)).1
  · intro z hz
    exact (hball (y := z) hz a (mem_univ a)).2
  · exact hh

end WeakMTWTransport

end

end OAI
