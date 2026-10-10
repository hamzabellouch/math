import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric Module
open scoped RealInnerProductSpace Topology ENNReal Pointwise
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def sphereChartScaleND (u : V) : ℝ := Real.sqrt (1-‖u‖^2/4)
noncomputable def sphereChartND (u : V) : WithLp 2 (V × ℝ) :=
  WithLp.toLp 2 (sphereChartScaleND u • u, 1-‖u‖^2/2)

omit [InnerProductSpace ℝ V] in
lemma sphereChartScaleND_pos {u : V} (hu : ‖u‖ < 2) :
    0 < sphereChartScaleND u := by
  apply Real.sqrt_pos.mpr
  nlinarith [norm_nonneg u]

omit [InnerProductSpace ℝ V] in
lemma sphereChartScaleND_sq {u : V} (hu : ‖u‖ ≤ 2) :
    sphereChartScaleND u ^ 2 = 1-‖u‖^2/4 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg u]

lemma sphereChartND_norm {u : V} (hu : ‖u‖ ≤ 2) :
    ‖sphereChartND u‖ = 1 := by
  have hs : 0 ≤ sphereChartScaleND u := Real.sqrt_nonneg _
  have he : ‖sphereChartND u‖^2 = 1 := by
    rw [sphereChartND, WithLp.prod_norm_sq_eq_of_L2]
    change ‖sphereChartScaleND u • u‖^2 + ‖(1-‖u‖^2/2:ℝ)‖^2 = 1
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [sphereChartScaleND_sq hu]
    ring
  nlinarith [norm_nonneg (sphereChartND u)]

lemma sphereChartND_mem_sphere {u : V} (hu : ‖u‖ ≤ 2) :
    sphereChartND u ∈ sphere (0 : WithLp 2 (V × ℝ)) 1 := by
  simpa only [mem_sphere, dist_zero_right] using sphereChartND_norm hu

lemma sphereChartND_phase (u : V) :
    inner ℝ (sphereChartND u) (WithLp.toLp 2 (0, (1:ℝ))) = 1-‖u‖^2/2 := by
  simp [sphereChartND,WithLp.prod_inner_apply]

lemma sphereChartND_north : sphereChartND (0:V) = WithLp.toLp 2 (0,(1:ℝ)) := by
  simp [sphereChartND]

lemma sphereChartND_snd_gt_neg_one {u : V} (hu : ‖u‖ < 2) :
    -1 < (WithLp.ofLp (sphereChartND u)).2 := by
  change -1 < 1-‖u‖^2/2
  nlinarith [norm_nonneg u]

noncomputable def sphereChartInvND (w : WithLp 2 (V × ℝ)) : V :=
  (Real.sqrt ((1+(WithLp.ofLp w).2)/2))⁻¹ • (WithLp.ofLp w).1

lemma sphereChartND_left_inv {u : V} (hu : ‖u‖ < 2) :
    sphereChartInvND (sphereChartND u) = u := by
  have hs : sphereChartScaleND u ≠ 0 := (sphereChartScaleND_pos hu).ne'
  have he : (1+(1-‖u‖^2/2))/2 = 1-‖u‖^2/4 := by ring
  simp only [sphereChartInvND, sphereChartND, WithLp.ofLp_toLp, he]
  change (sphereChartScaleND u)⁻¹ • (sphereChartScaleND u • u) = u
  rw [← mul_smul, inv_mul_cancel₀ hs, one_smul]

lemma sphereChartND_injOn : InjOn (sphereChartND : V → WithLp 2 (V × ℝ)) (ball 0 2) := by
  intro u hu v hv he
  have hu' : ‖u‖ < 2 := by simpa using hu
  have hv' : ‖v‖ < 2 := by simpa using hv
  have := congrArg sphereChartInvND he
  simpa [sphereChartND_left_inv hu', sphereChartND_left_inv hv'] using this

lemma sphereChartInvND_norm_sq {w : WithLp 2 (V × ℝ)} (hw : ‖w‖ = 1)
    (ht : -1 < (WithLp.ofLp w).2) :
    ‖sphereChartInvND w‖^2 = 2*(1-(WithLp.ofLp w).2) := by
  have hp : 0 < (1+(WithLp.ofLp w).2)/2 := by linarith
  have hs : Real.sqrt ((1+(WithLp.ofLp w).2)/2)^2 = (1+(WithLp.ofLp w).2)/2 :=
    Real.sq_sqrt hp.le
  have hn : ‖(WithLp.ofLp w).1‖^2 + ((WithLp.ofLp w).2)^2 = 1 := by
    have he := WithLp.prod_norm_sq_eq_of_L2 w
    rw [hw] at he
    simpa [Real.norm_eq_abs, sq_abs] using he.symm
  unfold sphereChartInvND
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, hs]
  field_simp [show 1+(WithLp.ofLp w).2 ≠ 0 by linarith]
  rw [div_eq_iff (show 1+(WithLp.ofLp w).2 ≠ 0 by linarith)]
  nlinarith [hn]

lemma sphereChartInvND_mem_ball {w : WithLp 2 (V × ℝ)} (hw : ‖w‖ = 1)
    (ht : -1 < (WithLp.ofLp w).2) : sphereChartInvND w ∈ ball (0:V) 2 := by
  have he := sphereChartInvND_norm_sq hw ht
  rw [mem_ball, dist_zero_right]
  nlinarith [norm_nonneg (sphereChartInvND w)]

lemma sphereChartND_right_inv {w : WithLp 2 (V × ℝ)} (hw : ‖w‖ = 1)
    (ht : -1 < (WithLp.ofLp w).2) : sphereChartND (sphereChartInvND w) = w := by
  have he := sphereChartInvND_norm_sq hw ht
  have hp : 0 < (1+(WithLp.ofLp w).2)/2 := by linarith
  have hs : Real.sqrt ((1+(WithLp.ofLp w).2)/2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hscale : sphereChartScaleND (sphereChartInvND w) =
      Real.sqrt ((1+(WithLp.ofLp w).2)/2) := by
    unfold sphereChartScaleND
    rw [he]
    congr 1
    ring
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change sphereChartScaleND (sphereChartInvND w) • sphereChartInvND w = (WithLp.ofLp w).1
    rw [hscale, sphereChartInvND, ← mul_smul, mul_inv_cancel₀ hs, one_smul]
  · change 1-‖sphereChartInvND w‖^2/2 = (WithLp.ofLp w).2
    rw [he]
    ring

lemma sphereChartScaleND_contDiffOn :
    ContDiffOn ℝ ⊤ (sphereChartScaleND : V → ℝ) (ball 0 2) := by
  apply ContDiffOn.sqrt
    ((contDiffOn_const.sub ((contDiff_norm_sq ℝ).contDiffOn.div_const 4)))
  intro u hu
  have hu' : ‖u‖ < 2 := by simpa using hu
  have : 0 < 1-‖u‖^2/4 := by nlinarith [norm_nonneg u]
  exact this.ne'

lemma sphereChartND_contDiffOn :
    ContDiffOn ℝ ⊤ (sphereChartND : V → WithLp 2 (V × ℝ)) (ball 0 2) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.contDiff.comp_contDiffOn
    ((sphereChartScaleND_contDiffOn.smul contDiffOn_id).prodMk
      (contDiffOn_const.sub ((contDiff_norm_sq ℝ).contDiffOn.div_const 2)))

lemma sphereChartScaleND_hasStrictFDerivAt {u : V} (hu : ‖u‖ < 2) :
    HasStrictFDerivAt sphereChartScaleND
      ((-1/(4*sphereChartScaleND u)) • innerSL ℝ u) u := by
  have hp : 0 < 1-‖u‖^2/4 := by nlinarith [norm_nonneg u]
  have hq : HasStrictFDerivAt (fun x : V => 1-‖x‖^2/4)
      ((-(1/2:ℝ)) • innerSL ℝ u) u := by
    convert! ((hasStrictFDerivAt_norm_sq u).mul_const (1/4:ℝ)).const_sub 1 using 1
    · funext x
      ring
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, neg_apply, smul_eq_mul]
      ring
  convert! hq.sqrt hp.ne' using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [sphereChartScaleND, smul_apply, smul_eq_mul]
  ring

noncomputable def sphereConeND (p : V × ℝ) : V × ℝ :=
  (p.2 • (sphereChartScaleND p.1 • p.1), p.2 * (1-‖p.1‖^2/2))

noncomputable def sphereConeDerivND (p : V × ℝ) : (V × ℝ) →L[ℝ] (V × ℝ) :=
  let u := p.1
  let r := p.2
  let s := sphereChartScaleND u
  let F := ContinuousLinearMap.fst ℝ V ℝ
  let T := ContinuousLinearMap.snd ℝ V ℝ
  let H := (innerSL ℝ u).comp F
  ((r*s) • F + (s • T - (r/(4*s)) • H).smulRight u).prod
    ((1-‖u‖^2/2) • T - r • H)

lemma sphereConeND_hasStrictFDerivAt {p : V × ℝ} (hp : ‖p.1‖ < 2) :
    HasStrictFDerivAt sphereConeND (sphereConeDerivND p) p := by
  have hs := (sphereChartScaleND_hasStrictFDerivAt hp).comp p hasStrictFDerivAt_fst
  have h₁ := hasStrictFDerivAt_snd.smul (hs.smul hasStrictFDerivAt_fst)
  have hv : HasStrictFDerivAt (fun x : V => 1-‖x‖^2/2) (-(innerSL ℝ p.1)) p.1 := by
    convert! ((hasStrictFDerivAt_norm_sq p.1).mul_const (1/2:ℝ)).const_sub 1 using 1
    · funext x
      ring
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, neg_apply, smul_eq_mul]
      ring
  have h₂ := (hasStrictFDerivAt_snd (𝕜 := ℝ)).mul
    (hv.comp p hasStrictFDerivAt_fst)
  convert! h₁.prodMk h₂ using 1
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · simp [sphereConeDerivND, smul_add, sub_smul, smul_smul]; module
  · simp [sphereConeDerivND]; ring

lemma sphereConeDerivND_apply (p z : V × ℝ) :
    sphereConeDerivND p z =
      ((p.2*sphereChartScaleND p.1) • z.1 +
         (sphereChartScaleND p.1*z.2-p.2/(4*sphereChartScaleND p.1)*inner ℝ p.1 z.1) • p.1,
       (1-‖p.1‖^2/2)*z.2-p.2*inner ℝ p.1 z.1) := by
  simp [sphereConeDerivND]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
