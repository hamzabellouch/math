import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicPrimitive
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCalculus

namespace OAI

/-! Canonical periodic primitives and angular derivatives in a smooth family. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

open CovarianceCorrector PeriodicPrimitive PeriodicCalculus

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def angleDerivative (F : A × ℝ → E) (z : A × ℝ) : E :=
  fderiv ℝ F z (0, 1)

lemma contDiff_angleDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (angleDerivative F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma angle_hasDerivAt {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : A) (t : ℝ) :
    HasDerivAt (fun s => F (p, s)) (angleDerivative F (p, t)) t := by
  have hi : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ A ℝ) t := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inr ℝ A ℝ).hasFDerivAt (x := t)).add_const (p, 0)
  have hd := ((hF.differentiable (by simp) (p, t)).hasFDerivAt.comp t hi).hasDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    angleDerivative] using hd

def bundle (f : ℝ → E) (hp : Function.Periodic f 1) (hc : Continuous f) : C(Period, E) :=
  ⟨hp.lift, continuous_coinduced_dom.mpr hc⟩

omit [NormedSpace ℝ E] in
@[simp] lemma bundle_apply (f : ℝ → E) (hp : Function.Periodic f 1) (hc : Continuous f)
    (t : ℝ) : bundle f hp hc (t : Period) = f t := rfl

def bundleFamily (F : A × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) : A → C(Period, E) :=
  fun p => bundle (fun t => F (p, t)) (hp p)
    (hF.continuous.comp (continuous_const.prodMk continuous_id))

@[simp] lemma bundleFamily_apply (F : A × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) (p : A) (t : ℝ) :
    bundleFamily F hF hp p (t : Period) = F (p, t) := rfl

lemma periodic_angleDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) (p : A) :
    Function.Periodic (fun t => angleDerivative F (p, t)) 1 := by
  have he : (fun t => angleDerivative F (p, t)) = deriv (fun t => F (p, t)) :=
    funext (fun t => (angle_hasDerivAt hF p t).deriv.symm)
  rw [he]
  exact periodic_deriv (hp p)

omit [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedSpace ℝ E] in
lemma periodic_lift (F : A → C(Period, E)) (p : A) :
    Function.Periodic (fun t : ℝ => F p (t : Period)) 1 := by
  intro t
  change F p ((t + 1 : ℝ) : Period) = _
  rw [AddCircle.coe_add_period]

def derivativeFamily (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) : A → C(Period, E) :=
  bundleFamily (angleDerivative (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (contDiff_angleDerivative hF) (periodic_angleDerivative hF (periodic_lift F))

lemma derivativeFamily_hasDerivAt (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) (p : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (derivativeFamily F hF p (t : Period)) t :=
  angle_hasDerivAt hF p t

lemma derivativeFamily_smooth (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) :
    ContDiff ℝ ∞ (fun z : A × ℝ => derivativeFamily F hF z.1 (z.2 : Period)) :=
  contDiff_angleDerivative hF

variable [CompleteSpace E]

lemma derivativeFamily_mean_zero (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) (p : A) :
    (∫ t, derivativeFamily F hF p t ∂AddCircle.haarAddCircle) = 0 := by
  rw [← integral_lift_eq_haar]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => derivativeFamily_hasDerivAt F hF p t)
    (((derivativeFamily F hF p).continuous.comp (AddCircle.continuous_mk' 1)).intervalIntegrable 0 1)]
  exact sub_eq_zero.mpr (by simpa using periodic_lift F p 0)

variable [FiniteDimensional ℝ A]

def primitiveFamily (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) : A → C(Period, E) :=
  bundleFamily (fun z : A × ℝ => primitive (fun t : ℝ => F z.1 (t : Period)) z.2)
    (contDiff_primitive_joint hF) (fun p => primitive_periodic
      ((F p).continuous.comp (AddCircle.continuous_mk' 1)) (periodic_lift F p)
      ((integral_lift_eq_haar (F p)).trans (hm p)))

@[simp] lemma primitiveFamily_apply (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) (p : A) (t : ℝ) :
    primitiveFamily F hF hm p (t : Period) = primitive (fun s : ℝ => F p (s : Period)) t := rfl

lemma primitiveFamily_smooth (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) :
    ContDiff ℝ ∞ (fun z : A × ℝ => primitiveFamily F hF hm z.1 (z.2 : Period)) :=
  contDiff_primitive_joint hF

lemma primitiveFamily_hasDerivAt (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) (p : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveFamily F hF hm p (s : Period)) (F p (t : Period)) t :=
  primitive_hasDerivAt ((F p).continuous.comp (AddCircle.continuous_mk' 1)) t

lemma primitiveFamily_mean_zero (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) (p : A) :
    (∫ t, primitiveFamily F hF hm p t ∂AddCircle.haarAddCircle) = 0 := by
  rw [← integral_lift_eq_haar]
  exact primitive_mean_zero ((F p).continuous.comp (AddCircle.continuous_mk' 1))

lemma derivativeFamily_primitiveFamily (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) :
    derivativeFamily (primitiveFamily F hF hm) (primitiveFamily_smooth F hF hm) = F := by
  funext p
  ext t
  refine Quotient.inductionOn' t ?_
  intro x
  exact (derivativeFamily_hasDerivAt _ (primitiveFamily_smooth F hF hm) p x).unique
    (primitiveFamily_hasDerivAt F hF hm p x)

end ClosedSurfaceR4.SmoothPeriodicCalculus

end

end OAI
