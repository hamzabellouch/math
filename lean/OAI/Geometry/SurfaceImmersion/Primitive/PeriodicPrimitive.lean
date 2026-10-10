import Mathlib

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rawPrimitive (f : ℝ → E) (x : ℝ) : E := ∫ t in 0..x, f t

def primitive (f : ℝ → E) (x : ℝ) : E :=
  rawPrimitive f x - ∫ t in 0..1, rawPrimitive f t

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem rawPrimitive_continuous {f : ℝ → E} (hf : Continuous f) :
    Continuous (rawPrimitive f) :=
  (show Differentiable ℝ (rawPrimitive f) from
    fun x => (rawPrimitive_hasDerivAt hf x).differentiableAt).continuous

theorem rawPrimitive_contDiff {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rawPrimitive f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (rawPrimitive_hasDerivAt hf.continuous x).differentiableAt, ?_⟩
  have he : deriv (rawPrimitive f) = f := by
    funext x
    exact (rawPrimitive_hasDerivAt hf.continuous x).deriv
  rwa [he]

omit [CompleteSpace E] in
theorem rawPrimitive_periodic {f : ℝ → E} (hf : Continuous f)
    (hperiod : Function.Periodic f 1) (hmean : (∫ t in 0..1, f t) = 0) :
    Function.Periodic (rawPrimitive f) 1 := by
  intro x
  unfold rawPrimitive
  rw [hperiod.intervalIntegral_add_eq_add 0 x (fun a b => hf.intervalIntegrable a b)]
  simp only [zero_add, hmean, add_zero]

theorem primitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  (rawPrimitive_hasDerivAt hf x).sub_const _

theorem primitive_continuous {f : ℝ → E} (hf : Continuous f) :
    Continuous (primitive f) :=
  (rawPrimitive_continuous hf).sub continuous_const

theorem primitive_contDiff {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (primitive f) :=
  (rawPrimitive_contDiff hf).sub contDiff_const

omit [CompleteSpace E] in
theorem primitive_periodic {f : ℝ → E} (hf : Continuous f)
    (hperiod : Function.Periodic f 1) (hmean : (∫ t in 0..1, f t) = 0) :
    Function.Periodic (primitive f) 1 := by
  intro x
  simp only [primitive, rawPrimitive_periodic hf hperiod hmean x]

theorem primitive_mean_zero {f : ℝ → E} (hf : Continuous f) :
    (∫ t in 0..1, primitive f t) = 0 := by
  unfold primitive
  rw [intervalIntegral.integral_sub
    ((rawPrimitive_continuous hf).intervalIntegrable 0 1) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul, sub_self]

/-- A smooth mean-zero periodic function has a smooth mean-zero periodic
primitive, with no solvability hypothesis beyond its vanishing mean. -/
theorem exists_smooth_periodic_primitive {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (hperiod : Function.Periodic f 1) (hmean : (∫ t in 0..1, f t) = 0) :
    ∃ F : ℝ → E, ContDiff ℝ ∞ F ∧ Function.Periodic F 1 ∧
      (∀ x, HasDerivAt F (f x) x) ∧ (∫ t in 0..1, F t) = 0 :=
  ⟨primitive f, primitive_contDiff hf, primitive_periodic hf.continuous hperiod hmean,
    primitive_hasDerivAt hf.continuous, primitive_mean_zero hf.continuous⟩

omit [CompleteSpace E] in
theorem integral_lift_eq_haar (f : UnitAddCircle → E) :
    (∫ t in 0..1, f (t : UnitAddCircle)) = ∫ t, f t ∂AddCircle.haarAddCircle := by
  calc
    _ = ∫ t : UnitAddCircle, f t := by
      simpa only [zero_add] using UnitAddCircle.intervalIntegral_preimage 0 f
    _ = _ := by simpa only [inv_one, one_smul] using
      (AddCircle.integral_haarAddCircle (f := f)).symm

/-- Vanishing normalized Haar mean gives a smooth mean-zero periodic primitive. -/
theorem exists_smooth_primitive_of_haar_mean_zero {f : UnitAddCircle → E}
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f (t : UnitAddCircle)))
    (hmean : (∫ t, f t ∂AddCircle.haarAddCircle) = 0) :
    ∃ F : ℝ → E, ContDiff ℝ ∞ F ∧ Function.Periodic F 1 ∧
      (∀ x : ℝ, HasDerivAt F (f (x : UnitAddCircle)) x) ∧ (∫ t in 0..1, F t) = 0 := by
  apply exists_smooth_periodic_primitive hf
  · intro x
    change f ((x + 1 : ℝ) : UnitAddCircle) = f (x : UnitAddCircle)
    rw [AddCircle.coe_add_period]
  · rw [integral_lift_eq_haar, hmean]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
