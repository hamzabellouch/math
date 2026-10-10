import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.FullSet

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_with_acceleration {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_apply,add_comm] using H

lemma HasSecondTaylor.smooth_support_diag_le {f q : E → ℝ}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasSecondTaylor f l B) (hfd : HasFDerivAt f l 0)
    (hq : ContDiffAt ℝ 2 q 0) (hval : q 0=f 0)
    (hlo : q≤ᶠ[𝓝 0] f) (d:E) :
    fderiv ℝ (fderiv ℝ q) 0 d d≤B d d := by
  have hmin : IsLocalMin (fun x => f x-q x) 0 := by
    filter_upwards [hlo] with x hx
    change f 0-q 0≤f x-q x
    rw [hval,sub_self]
    linarith only [hx]
  have hlin := hmin.hasFDerivAt_eq_zero
    (hfd.sub (hq.differentiableAt (by norm_num)).hasFDerivAt)
  have Hj := hf.sub (hasSecondTaylor_of_contDiffAt hq)
  rw [hlin] at Hj
  let remainder := B - fderiv ℝ (fderiv ℝ q) 0
  have hnonneg : 0 ≤ remainder d d := by
    by_contra hnegative
    have hnegative : remainder d d < 0 := lt_of_not_ge hnegative
    have hdir : d ≠ 0 := by
      intro hzero
      subst d
      simp at hnegative
    have hnorm : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdir)
    let epsilon := -(remainder d d) / (4 * ‖d‖ ^ 2)
    have hepsilon : 0 < epsilon := div_pos (neg_pos.mpr hnegative) (by positivity)
    have hepsilon_mul : epsilon * ‖d‖ ^ 2 = -(remainder d d) / 4 := by
      dsimp [epsilon]
      field_simp
    obtain ⟨radius, hradius, hball⟩ :=
      Metric.eventually_nhds_iff.mp ((Hj.eventually hepsilon).and hmin)
    let delta := radius / (2 * (‖d‖ + 1))
    have hdelta : 0 < delta := div_pos hradius (by positivity)
    have hdelta_mul : delta * (2 * (‖d‖ + 1)) = radius :=
      div_mul_cancel₀ _ (by positivity)
    have hmem : delta • d ∈ Metric.ball (0 : E) radius := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hdelta]
      nlinarith [norm_nonneg d]
    obtain ⟨htaylor, hminimum⟩ := hball hmem
    change |f (delta • d) - q (delta • d) - (f 0 - q 0) - 0 -
      remainder (delta • d) (delta • d) / 2| ≤ epsilon * ‖delta • d‖ ^ 2 at htaylor
    have hbilinear : remainder (delta • d) (delta • d) = delta ^ 2 * remainder d d := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hscaled_norm : ‖delta • d‖ ^ 2 = delta ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdelta, mul_pow]
    rw [hbilinear, hscaled_norm] at htaylor
    have hupper := (abs_le.mp htaylor).2
    have hscaled_error : epsilon * (delta ^ 2 * ‖d‖ ^ 2) =
        delta ^ 2 * (-(remainder d d) / 4) := by
      calc
        _ = delta ^ 2 * (epsilon * ‖d‖ ^ 2) := by ring
        _ = _ := by rw [hepsilon_mul]
    rw [hscaled_error] at hupper
    have hstrict := mul_neg_of_pos_of_neg (sq_pos_of_pos hdelta) hnegative
    change f 0 - q 0 ≤ f (delta • d) - q (delta • d) at hminimum
    nlinarith
  change 0 ≤ B d d - fderiv ℝ (fderiv ℝ q) 0 d d at hnonneg
  linarith only [hnonneg]

lemma HasSecondTaylor.smooth_support_diag_le_at {f q : E → ℝ} {x : E}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasSecondTaylor (fun h => f (x+h)) l B) (hfd : HasFDerivAt f l x)
    (hq : ContDiffAt ℝ 2 q x) (hval : q x=f x)
    (hlo : q≤ᶠ[𝓝 x] f) (d:E) :
    fderiv ℝ (fderiv ℝ q) x d d≤B d d := by
  have hc : ContinuousAt (fun h:E => x+h) 0 := continuousAt_const.add continuousAt_id
  have hq' : ContDiffAt ℝ 2 (fun h:E => q (x+h)) 0 := by
    exact (show ContDiffAt ℝ 2 q (x+0) by simpa only [add_zero] using hq).comp 0
      (contDiffAt_const.add contDiffAt_id)
  have hd : HasFDerivAt (fun h:E => f (x+h)) l 0 := by
    exact (hasFDerivAt_comp_add_left x).mpr (by simpa only [add_zero] using hfd)
  have hv : q (x+0)=f (x+0) := by simpa only [add_zero] using hval
  have hh : (fun h:E => q (x+h))≤ᶠ[𝓝 0] (fun h => f (x+h)) := by
    have ht : Tendsto (fun h:E => x+h) (𝓝 0) (𝓝 x) := by
      simpa only [add_zero] using hc.tendsto
    exact ht.eventually hlo
  have H := hf.smooth_support_diag_le hd hq' hv hh d
  have he : fderiv ℝ (fun h:E => q (x+h))=(fun h => fderiv ℝ q (x+h)) :=
    funext (fun h => fderiv_comp_add_left x)
  rw [he,fderiv_comp_add_left,add_zero] at H
  exact H

lemma bilinear_diag_sub_bound (B C : E →L[ℝ] E →L[ℝ] ℝ) (d:E) :
    |B d d-C d d|≤‖B-C‖*‖d‖^2 := by
  have H := (B-C).le_opNorm₂ d d
  simpa only [sub_apply,Real.norm_eq_abs,pow_two,mul_assoc] using H
end WeakMTWTransport

end

end OAI
