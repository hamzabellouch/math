import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformDeformation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Asymptotics.Lemmas

namespace OAI

/-! Positive deformation of the actual Cartesian radial velocity field. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialScalarField_hasFDerivAt_zero (q : ℝ → ℝ) (hq : ContinuousAt q 0) :
    HasFDerivAt (fun x : E => q ‖x‖ • x) (q 0 • ContinuousLinearMap.id ℝ E) 0 := by
  apply HasFDerivAt.of_isLittleO
  have hc : ContinuousAt (fun x : E => q ‖x‖) 0 := by
    have hn : ContinuousAt (fun x : E => ‖x‖) 0 := continuous_norm.continuousAt
    simpa only [Function.comp_def] using hq.comp_of_eq hn (by simp)
  have hh := (hc.isLittleO (F := ℝ)).smul_isBigO
    (Asymptotics.isBigO_refl (fun x : E => x) (nhds 0))
  simpa [Pi.smul_apply,sub_smul] using hh

theorem radial_norm_fderiv_apply (x v : E) (hx : x ≠ 0) :
    fderiv ℝ (fun y : E => ‖y‖) x v=inner ℝ x v/‖x‖ := by
  have hn := (contDiffAt_norm ℝ hx (n := 1)).differentiableAt one_ne_zero
  have hh := hn.hasFDerivAt.mul hn.hasFDerivAt
  have hs : HasFDerivAt (fun y : E => ‖y‖*‖y‖) (2 • innerSL ℝ x) x := by
    simpa only [pow_two] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hh.unique hs)
  simp only [add_apply,smul_apply,
    smul_eq_mul,innerSL_apply_apply,two_smul] at he
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  nlinarith

theorem radialScalarField_fderiv (q : ℝ → ℝ) (x v : E) (hx : x ≠ 0)
    (hq : DifferentiableAt ℝ q ‖x‖) :
    fderiv ℝ (fun y : E => q ‖y‖ • y) x v=
      q ‖x‖ • v+(deriv q ‖x‖/‖x‖*inner ℝ x v) • x := by
  have hn := (contDiffAt_norm ℝ hx (n := 1)).differentiableAt one_ne_zero
  have hd := (hq.hasFDerivAt.comp x hn.hasFDerivAt).smul (hasFDerivAt_id x)
  simp only [Function.comp_apply,id_eq] at hd
  change HasFDerivAt (fun y : E => q ‖y‖ • y) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,fderiv_eq_smul_deriv,smul_eq_mul]
  rw [radial_norm_fderiv_apply x v hx]
  congr 1
  congr 1
  ring

theorem radialScalarField_positive (q : ℝ → ℝ) (x v : E) (hx : x ≠ 0)
    (hq : DifferentiableAt ℝ q ‖x‖) (c : ℝ)
    (ht : c ≤ q ‖x‖) (hr : c ≤ q ‖x‖+‖x‖*deriv q ‖x‖) :
    c*‖v‖^2 ≤ inner ℝ (fderiv ℝ (fun y : E => q ‖y‖ • y) x v) v := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc := abs_real_inner_le_norm x v
  have hsq : (inner ℝ x v)^2 ≤ ‖x‖^2*‖v‖^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (inner ℝ x v))
      (mul_nonneg (norm_nonneg x) (norm_nonneg v))).mpr hc
    simpa only [sq_abs,mul_pow] using hh
  let t := (inner ℝ x v)^2/‖x‖^2
  have ht0 : 0 ≤ t := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have htv : t ≤ ‖v‖^2 := (div_le_iff₀ (sq_pos_of_pos hxp)).mpr (by nlinarith [hsq])
  rw [radialScalarField_fderiv q x v hx hq,inner_add_left,real_inner_smul_left,
    real_inner_smul_left,real_inner_self_eq_norm_sq]
  have hid : q ‖x‖*‖v‖^2+(deriv q ‖x‖/‖x‖*inner ℝ x v)*inner ℝ x v=
      q ‖x‖*(‖v‖^2-t)+(q ‖x‖+‖x‖*deriv q ‖x‖)*t := by
    dsimp [t]
    field_simp [hxp.ne']
    ring
  rw [hid]
  have h1 := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr htv)
  have h2 := mul_le_mul_of_nonneg_right hr ht0
  nlinarith

noncomputable def radialMatchedVectorField (n : ℕ) (z : ProfileMatchingBall) (x : E) : E :=
  radialVelocityRatio (6-2*radialShootingA n) (fun r => ‖radialMatchedProfile n z r‖) ‖x‖ • x

theorem radialMatchedVectorField_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ x v : E,
        c*‖v‖^2 ≤ inner ℝ (fderiv ℝ (radialMatchedVectorField n z) x v) v := by
  obtain ⟨c,hc,he⟩ := radialMatched_uniform_deformation
  refine ⟨c,hc,?_⟩
  filter_upwards [he] with n hn z hX hz x v
  let A := fun r => ‖radialMatchedProfile n z r‖
  let q := radialVelocityRatio (6-2*radialShootingA n) A
  have hA : Continuous A := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  by_cases hx : x=0
  · subst x
    have hAn : A 0 ≠ 0 := norm_ne_zero_iff.mpr
      (radialMatchedProfile_ne_zero n z hX 0 le_rfl)
    have hq : ContinuousAt q 0 :=
      (continuous_const.mul (continuous_radialAverage _ (hA.pow 2))).continuousAt.div
        (hA.pow 2).continuousAt (pow_ne_zero 2 hAn)
    change c*‖v‖^2 ≤ inner ℝ (fderiv ℝ (fun y : E => q ‖y‖ • y) 0 v) v
    rw [(radialScalarField_hasFDerivAt_zero q hq).fderiv]
    simp only [smul_apply,ContinuousLinearMap.id_apply,
      real_inner_smul_left,real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (hn z hX hz 0 le_rfl).2 (sq_nonneg _)
  · have hrp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hAr : A ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr
      (radialMatchedProfile_ne_zero n z hX ‖x‖ (norm_nonneg _))
    have hdA := (((radialMatchedAmplitude_contDiffOn n z hX hz) ‖x‖ hrp).contDiffAt
      (Ioi_mem_nhds hrp)).differentiableAt (by simp)
    have hdq : DifferentiableAt ℝ q ‖x‖ :=
      ((differentiableAt_const (6-2*radialShootingA n)).mul (hasDerivAt_radialAverage _ (hA.pow 2) ‖x‖ hrp.ne').differentiableAt).div
        (hdA.pow 2) (pow_ne_zero 2 hAr)
    have hw := (hasDerivAt_id ‖x‖).mul hdq.hasDerivAt
    simp only [one_mul,id_eq] at hw
    change HasDerivAt (radialMatchedVelocity n z) (q ‖x‖+‖x‖*deriv q ‖x‖) ‖x‖ at hw
    apply radialScalarField_positive q x v hx hdq c (hn z hX hz ‖x‖ (norm_nonneg _)).2
    rw [← hw.deriv]
    exact (hn z hX hz ‖x‖ (norm_nonneg _)).1

end DefocusingNLS

end OAI
