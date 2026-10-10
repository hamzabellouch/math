import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive
import OAI.Geometry.SurfaceImmersion.Correction.CovarianceCorrector

namespace OAI

/-! Differentiation and normalized integration on the period circle. -/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCalculus

open CovarianceCorrector PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The real primitive descends to the circle without losing smoothness or
its normalization. -/
theorem exists_circle_primitive {f : Period → E}
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f (t : Period)))
    (hm : (∫ t, f t ∂AddCircle.haarAddCircle) = 0) :
    ∃ F : Period → E, Continuous F ∧
      ContDiff ℝ ∞ (fun t : ℝ => F (t : Period)) ∧
      (∫ t, F t ∂AddCircle.haarAddCircle) = 0 ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (s : Period)) (f (t : Period)) t := by
  obtain ⟨F, hF, hp, hd, hmF⟩ := exists_smooth_primitive_of_haar_mean_zero hf hm
  refine ⟨hp.lift, continuous_coinduced_dom.mpr hF.continuous, ?_, ?_, ?_⟩
  · simpa only [Function.Periodic.lift_coe] using hF
  · rw [← integral_lift_eq_haar]
    simpa only [Function.Periodic.lift_coe] using hmF
  · simpa only [Function.Periodic.lift_coe] using hd

omit [CompleteSpace E] in
lemma periodic_deriv {f : ℝ → E} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun t => f (t + 1)) = f := funext hp
  have hd := congrArg (fun g : ℝ → E => deriv g x) he
  simpa only [deriv_comp_add_const] using hd

/-- A smooth circle function has a smooth circle derivative of mean zero. -/
theorem exists_circle_derivative {f : Period → E}
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f (t : Period))) :
    ∃ D : Period → E, Continuous D ∧
      ContDiff ℝ ∞ (fun t : ℝ => D (t : Period)) ∧
      (∫ t, D t ∂AddCircle.haarAddCircle) = 0 ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (s : Period)) (D (t : Period)) t := by
  let g : ℝ → E := fun t => f (t : Period)
  have hg : ContDiff ℝ ∞ g := hf
  have hp : Function.Periodic g 1 := by
    intro x
    change f ((x + 1 : ℝ) : Period) = f (x : Period)
    rw [AddCircle.coe_add_period]
  have hD : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  let D : Period → E := (periodic_deriv hp).lift
  have hDc : Continuous D := continuous_coinduced_dom.mpr hD.continuous
  have hd (t : ℝ) : HasDerivAt g (D (t : Period)) t :=
    (hg.differentiable (by simp) t).hasDerivAt
  refine ⟨D, hDc, ?_, ?_, hd⟩
  · simpa only [D, Function.Periodic.lift_coe] using hD
  · rw [← integral_lift_eq_haar]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((hD.continuous).intervalIntegrable 0 1)]
    exact sub_eq_zero.mpr (by simpa using hp 0)

end ClosedSurfaceR4.PeriodicCalculus

end

end OAI
