import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Ball Submean. -/

section

 

noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ContDiff InnerProductSpace
namespace PotentialABP

section Affine
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessian_affine_comp {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (c : F) (z u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (c + L y))) z u v =
      fderiv ℝ (fderiv ℝ f) (c + L z) (L u) (L v) := by
  have hd : fderiv ℝ (fun y => c + L y) = fun _ => L := by
    funext y
    exact (L.hasFDerivAt.const_add c).fderiv
  have hc : ContDiff ℝ ∞ (fun y => c + L y) := contDiff_const.add L.contDiff
  change fderiv ℝ (fderiv ℝ (f ∘ (fun y => c + L y))) z u v = _
  rw [PotentialKaehler.second_derivative_comp hc.contDiffAt hf.contDiffAt, hd]
  simp

end Affine

section ComplexHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
local instance ballSubmeanRealInnerProductSpace : InnerProductSpace ℝ E :=
  InnerProductSpace.rclikeToReal ℂ E

private def unitScalarIso (a : ℂ) (ha : ‖a‖ = 1) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ E a (by
    intro h; simp [h] at ha)).restrictScalars ℝ
  norm_map' x := by simp [LinearEquiv.smulOfNeZero_apply, norm_smul, ha]

lemma ball_integral_unit_smul (f : E → ℝ) (r : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ∫ x in ball (0:E) r, f (a • x) = ∫ x in ball (0:E) r, f x := by
  let e : E ≃ₗᵢ[ℝ] E := unitScalarIso a ha
  have hb : e ⁻¹' ball (0:E) r = ball (0:E) r := by
    ext x
    simp only [mem_preimage, mem_ball, dist_zero_right, e.norm_map]
  have hm := e.measurePreserving.restrict_preimage (s := ball (0:E) r) isOpen_ball.measurableSet
  rw [hb] at hm
  exact hm.integral_comp e.toHomeomorph.measurableEmbedding f

lemma ball_integral_translate (f : E → ℝ) (c : E) (r : ℝ) :
    ∫ x in ball (0:E) r, f (c+x) = ∫ x in ball c r, f x := by
  have hb : (fun x : E => c+x) ⁻¹' ball c r = ball (0:E) r := by
    ext x
    simp [mem_ball, dist_eq_norm]
  have hm := (measurePreserving_add_left (volume : Measure E) c).restrict_preimage
    (s := ball c r) isOpen_ball.measurableSet
  rw [hb] at hm
  exact hm.integral_comp (Homeomorph.addLeft c).measurableEmbedding f

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
lemma complexLine_hessian {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (c v : E) (z a b : ℂ) :
    fderiv ℝ (fderiv ℝ (fun w : ℂ => f (c + w • v))) z a b =
      fderiv ℝ (fderiv ℝ f) (c + z • v) (a • v) (b • v) := by
  let L : ℂ →L[ℝ] E := ((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ
  exact hessian_affine_comp hf L c z a b

 

theorem smooth_ball_submean {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : E) {R : ℝ} (hR : 0 ≤ R)
    (hlevi : ∀ x ∈ closedBall c R, ∀ v : E,
      0 ≤ fderiv ℝ (fderiv ℝ f) x v v +
        fderiv ℝ (fderiv ℝ f) x (Complex.I • v) (Complex.I • v)) :
    (volume.real (ball (0:E) R)) * f c ≤ ∫ x in ball c R, f x := by
  let F : ℝ → E → ℝ := fun θ v => f (c + circleMap 0 1 θ • v)
  have hF : Continuous (Function.uncurry F) := hf.continuous.comp
    (continuous_const.add (((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd))
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc 0 (2*Real.pi))).prod
        (volume.restrict (ball (0:E) R))) := by
    rw [Measure.prod_restrict]
    apply (hF.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod (isCompact_closedBall (0:E) R))).mono_set
    exact prod_mono uIoc_subset_uIcc ball_subset_closedBall
  have hv (v : E) (hv : v ∈ ball (0:E) R) :
      2*Real.pi*f c ≤ ∫ θ in 0..2*Real.pi, F θ v := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ => f (c + z • v)) :=
      hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have h := smooth_circle_submean hc 0 (by norm_num : (0:ℝ) ≤ 1) ?_
    · simp only [zero_smul, add_zero] at h
      unfold Real.circleAverage at h
      simp only [smul_eq_mul] at h
      exact (le_inv_mul_iff₀ (by positivity : 0 < 2*Real.pi)).mp h
    · intro z hz
      rw [complexLine_hessian hf, complexLine_hessian hf, one_smul]
      apply hlevi
      have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
      have hv' : ‖v‖ ≤ R := (by simpa [mem_ball] using hv : ‖v‖ < R).le
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact (mul_le_mul_of_nonneg_left hv' (norm_nonneg z)).trans
        (mul_le_of_le_one_left hR hz')
  have hmean : (2*Real.pi) * (volume.real (ball (0:E) R) * f c) ≤
      ∫ v in ball (0:E) R, ∫ θ in 0..2*Real.pi, F θ v := by
    have hi' : IntegrableOn (fun v => ∫ θ in 0..2*Real.pi, F θ v) (ball (0:E) R) := by
      simpa only [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi),
        uIoc_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi), Function.uncurry_def,
        IntegrableOn] using hi.integral_prod_right
    have hiC : IntegrableOn (fun _ : E => 2*Real.pi*f c) (ball (0:E) R) :=
      (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall (0:E) R)).mono_set
        ball_subset_closedBall
    have hm := setIntegral_mono_on hiC hi' isOpen_ball.measurableSet hv
    simpa only [setIntegral_const, smul_eq_mul, mul_left_comm] using hm
  rw [← intervalIntegral_integral_swap hi] at hmean
  have he (θ : ℝ) : (∫ v in ball (0:E) R, F θ v) = ∫ x in ball c R, f x := by
    exact (ball_integral_unit_smul (fun x => f (c+x)) R (circleMap 0 1 θ)
      (by simp)).trans (ball_integral_translate f c R)
  simp_rw [he] at hmean
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmean
  nlinarith [Real.pi_pos]

end ComplexHilbert
end PotentialABP

end
end

end OAI
