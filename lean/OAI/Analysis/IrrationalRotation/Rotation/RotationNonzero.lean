import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

noncomputable section
namespace Invariant233.Rotation
open MeasureTheory

theorem representation_on_vector_ae (θ : ℝ) (a : C(Circle, ℂ)) (f : Hilbert) :
    representation θ a f =ᵐ[circleMeasure]
      fun x => WeightedShift.diagonal (orbitWeight θ a x) (f x) := by
  exact WeightedShift.fieldDiagonalVec_ae (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
    (fun k => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable) f

theorem representation_vacuum_eq_zero_iff (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a vacuum = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hout : representation θ a vacuum =ᵐ[circleMeasure] (fun _ => (0 : Fiber)) := by
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have hc : vacuum =ᵐ[circleMeasure] (fun _ => lp.single 2 (0 : ℤ) (1 : ℂ)) :=
      Lp.coeFn_const 2 circleMeasure _
    have hae : (fun x : Circle => a x) =ᵐ[circleMeasure] (fun _ => (0 : ℂ)) := by
      filter_upwards [representation_on_vector_ae θ a vacuum, hc, hout] with x hx hc hz
      have heq := congrArg (fun v : Fiber => v (0 : ℤ)) (hx.symm.trans hz)
      change a (action θ 0 x) * vacuum x 0 = 0 at heq
      simpa [hc, action, lp.coeFn_single] using heq
    let : circleMeasure.IsOpenPosMeasure := by
      unfold circleMeasure
      infer_instance
    apply ContinuousMap.coe_injective
    exact Measure.eq_of_ae_eq hae a.continuous continuous_const
  · intro h
    subst a
    apply Lp.ext
    filter_upwards [representation_on_vector_ae θ 0 vacuum, Lp.coeFn_zero Fiber 2 circleMeasure]
      with x hx hz
    rw [hx, hz]
    ext k
    change (0 : C(Circle, ℂ)) (action θ k x) * vacuum x k = 0
    simp

theorem representation_eq_zero_iff (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (representation_vacuum_eq_zero_iff θ a).1
    simp [h]
  · intro h
    subst a
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [representation_on_vector_ae θ 0 f, Lp.coeFn_zero Fiber 2 circleMeasure]
      with x hx hz
    change (representation θ 0 f) x = (0 : Hilbert) x
    rw [hx, hz]
    ext k
    change (0 : C(Circle, ℂ)) (action θ k x) * f x k = 0
    simp

theorem fiberShift_operator_injective : Function.Injective U := by
  intro f g h
  apply Lp.ext
  filter_upwards [
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL f,
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL g]
    with x hf hg
  apply (WeightedShift.shift 1).injective
  calc
    WeightedShift.shift 1 (f x) = U f x := hf.symm
    _ = U g x := congrArg (fun v : Hilbert => v x) h
    _ = WeightedShift.shift 1 (g x) := hg

theorem weighted_eq_zero_iff (θ : ℝ) (a : C(Circle, ℂ)) :
    weighted θ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (representation_eq_zero_iff θ a).1
    apply ContinuousLinearMap.ext
    intro f
    apply fiberShift_operator_injective
    have heq := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f) h
    simpa [weighted] using heq
  · intro h
    rw [weighted, (representation_eq_zero_iff θ a).2 h, mul_zero]

theorem weighted_ne_zero (θ : ℝ) {a : C(Circle, ℂ)} (ha : a ≠ 0) :
    weighted θ a ≠ 0 := (weighted_eq_zero_iff θ a).not.mpr ha

theorem weightedReal_eq_zero_iff (θ : ℝ) (f : C(Circle, ℝ)) :
    weightedReal θ f = 0 ↔ f = 0 := by
  rw [weightedReal, weighted_eq_zero_iff]
  constructor
  · intro h
    apply ContinuousMap.ext
    intro x
    have hx := congrArg (fun a : C(Circle, ℂ) => a x) h
    simpa [complexWeight] using hx
  · intro h
    subst f
    apply ContinuousMap.ext
    intro x
    simp [complexWeight]

end Invariant233.Rotation

end

end OAI
