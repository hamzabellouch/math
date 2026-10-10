import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCalculus
import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral

namespace OAI

/-! Slow differentiation commutes with the periodic mean. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def slowDerivative (F : A × ℝ → E) (v : A) (z : A × ℝ) : E :=
  fderiv ℝ F z (v, 0)

lemma contDiff_slowDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (v : A) :
    ContDiff ℝ ∞ (slowDerivative F v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma fderiv_slice {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (p v : A) (t : ℝ) :
    fderiv ℝ (fun q => F (q, t)) p v = slowDerivative F v (p, t) := by
  rw [(SmoothParameterIntegral.partial_hasFDerivAt hF p t).fderiv]
  rfl

lemma periodic_slowDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) (v p : A) :
    Function.Periodic (fun t => slowDerivative F v (p, t)) 1 := by
  intro t
  have he : (fun q => F (q, t + 1)) = fun q => F (q, t) := funext (fun q => hp q t)
  have hd := congrArg (fun f : A → E => fderiv ℝ f p v) he
  simpa only [fderiv_slice hF] using hd

def slowDerivativeFamily (F : A → C(CovarianceCorrector.Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period))) (v : A) :
    A → C(CovarianceCorrector.Period, E) :=
  bundleFamily (slowDerivative (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period)) v)
    (contDiff_slowDerivative hF v) (periodic_slowDerivative hF (periodic_lift F) v)

lemma slowDerivativeFamily_smooth (F : A → C(CovarianceCorrector.Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period))) (v : A) :
    ContDiff ℝ ∞ (fun z : A × ℝ => slowDerivativeFamily F hF v z.1
      (z.2 : CovarianceCorrector.Period)) := contDiff_slowDerivative hF v

variable [FiniteDimensional ℝ A]

lemma slowDerivativeFamily_mean_zero (F : A → C(CovarianceCorrector.Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) (v p : A) :
    (∫ t, slowDerivativeFamily F hF v p t ∂AddCircle.haarAddCircle) = 0 := by
  let f : A × ℝ → E := fun z => F z.1 (z.2 : CovarianceCorrector.Period)
  have hzero : (fun p => ∫ t in 0..1, f (p, t)) = fun _ => (0 : E) := by
    funext q
    exact (PeriodicPrimitive.integral_lift_eq_haar (F q)).trans (hm q)
  have hd := (SmoothParameterIntegral.hasFDerivAt_integral hF 0 1 p).fderiv
  change fderiv ℝ (fun q => ∫ t in 0..1, f (q, t)) p = _ at hd
  rw [hzero, fderiv_const_apply] at hd
  have he := congrArg (fun L : A →L[ℝ] E => L v) hd.symm
  have hi := ContinuousLinearMap.intervalIntegral_apply (μ := volume)
    (φ := fun t => SmoothParameterIntegral.partialDerivative f (p, t))
    ((SmoothParameterIntegral.contDiff_partialDerivative hF).continuous.comp
      (continuous_const.prodMk continuous_id) |>.intervalIntegrable 0 1) v
  rw [← PeriodicPrimitive.integral_lift_eq_haar]
  change (∫ t in 0..1, slowDerivative f v (p, t)) = 0
  calc
    _ = (∫ t in 0..1, SmoothParameterIntegral.partialDerivative f (p, t)) v := hi.symm
    _ = 0 := he

end ClosedSurfaceR4.SmoothPeriodicCalculus

namespace ClosedSurfaceR4.PeriodicCorrector

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The differentiated pairing constraint in an arbitrary slow direction. -/
theorem directional_pairing_constraint {Y U : A → E} {H : A → ℝ}
    {p v : A} {C : E} {j : ℝ}
    (hY : DifferentiableAt ℝ Y p) (hU : DifferentiableAt ℝ U p)
    (hH : DifferentiableAt ℝ H p) (he : ∀ q, inner ℝ (Y q) (U q) = H q)
    (hC : fderiv ℝ Y p v = C)
    (hK : inner ℝ C (U p) = fderiv ℝ H p v - j) :
    inner ℝ (Y p) (fderiv ℝ U p v) = j := by
  have hd := hY.hasFDerivAt.inner ℝ hU.hasFDerivAt
  have hid : (fun q => inner ℝ (Y q) (U q)) = H := funext he
  rw [hid] at hd
  have hv := congrArg (fun L : A →L[ℝ] ℝ => L v) (hd.unique hH.hasFDerivAt)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply] at hv
  rw [hC] at hv
  linarith

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
