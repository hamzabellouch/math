import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Spectral.FieldResolventTransport

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

private theorem measurable_positive_orbit (θ : ℝ) (h : Circle → ℝ)
    (hm : Measurable h) (k : ℤ) :
    AEStronglyMeasurable (fun x => h (action θ k x)) circleMeasure :=
  (hm.comp (action_measurePreserving θ k).measurable).aestronglyMeasurable

theorem positiveFieldResolvent_mem_algebra
    (θ : ℝ) (h : Circle → ℝ) (hpos : ∀ x, 0 ≤ h x) (hm : Measurable h) :
    WeightedShift.positiveFieldResolvent (fun x k => h (action θ k x))
      (fun x k => hpos (action θ k x)) (measurable_positive_orbit θ h hm) ∈ algebra θ := by
  let g : Circle → ℂ := fun x => (((1 + h x)⁻¹ : ℝ) : ℂ)
  have hg : Measurable g := by
    exact ((measurable_const.add hm).inv).complex_ofReal
  have hb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    have ht : 0 < 1 + h x := by linarith [hpos x]
    change ‖(((1 + h x)⁻¹ : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht.le)]
    exact (inv_le_one₀ ht).mpr (by linarith [hpos x])
  have hR : WeightedShift.positiveFieldResolvent (fun x k => h (action θ k x))
      (fun x k => hpos (action θ k x)) (measurable_positive_orbit θ h hm) =
      measurableRepresentation θ g 1 (by norm_num) hg hb := by
    apply WeightedShift.fieldDiagonal_congr
    exact Eventually.of_forall fun x => lp.ext (funext fun k => rfl)
  rw [hR]
  exact measurableRepresentation_mem_algebra θ g 1 (by norm_num) hg hb

theorem positive_orbit_multiplier_domain_invariant
    (θ : ℝ) (h : Circle → ℝ) (hpos : ∀ x, 0 ≤ h x) (hm : Measurable h)
    (A : Hilbert →L[ℂ] Hilbert) (hA : A ∈ (algebra θ).commutant)
    (ξ : (WeightedShift.fieldUnboundedMultiplier circleMeasure
      (fun x k => (h (action θ k x) : ℂ))).domain) :
    A ξ.val ∈ (WeightedShift.fieldUnboundedMultiplier circleMeasure
      (fun x k => (h (action θ k x) : ℂ))).domain := by
  apply WeightedShift.fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent
    (fun x k => h (action θ k x)) (fun x k => hpos (action θ k x))
    (measurable_positive_orbit θ h hm) A
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp hA) _
    (positiveFieldResolvent_mem_algebra θ h hpos hm)).symm

theorem positive_orbit_multiplier_commutes
    (θ : ℝ) (h : Circle → ℝ) (hpos : ∀ x, 0 ≤ h x) (hm : Measurable h)
    (A : Hilbert →L[ℂ] Hilbert) (hA : A ∈ (algebra θ).commutant)
    (ξ : (WeightedShift.fieldUnboundedMultiplier circleMeasure
      (fun x k => (h (action θ k x) : ℂ))).domain) :
    WeightedShift.fieldUnboundedMultiplier circleMeasure
      (fun x k => (h (action θ k x) : ℂ))
      ⟨A ξ.val, positive_orbit_multiplier_domain_invariant θ h hpos hm A hA ξ⟩ =
      A (WeightedShift.fieldUnboundedMultiplier circleMeasure
        (fun x k => (h (action θ k x) : ℂ)) ξ) := by
  apply WeightedShift.fieldUnboundedMultiplier_commutes_of_commute_resolvent
    (fun x k => h (action θ k x)) (fun x k => hpos (action θ k x))
    (measurable_positive_orbit θ h hm) A
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp hA) _
    (positiveFieldResolvent_mem_algebra θ h hpos hm)).symm

theorem positive_orbit_transported_projection_mem
    (θ : ℝ) (h : Circle → ℝ) (hpos : ∀ x, 0 ≤ h x) (hm : Measurable h)
    (p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) :
    (InvariantRotation.AffiliatedTransport.transported
      (WeightedShift.fieldUnboundedMultiplier circleMeasure
        (fun x k => (h (action θ k x) : ℂ))) p.range).starProjection ∈ algebra θ :=
  WeightedShift.transported_projection_mem_of_resolvent_mem
    (fun x k => h (action θ k x)) (fun x k => hpos (action θ k x))
    (measurable_positive_orbit θ h hm) (algebra θ)
    (positiveFieldResolvent_mem_algebra θ h hpos hm) p hp

theorem exponential_orbit_transported_projection_mem
    (θ : ℝ) (b : Circle → ℝ) (hb : Measurable b)
    (p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) :
    (InvariantRotation.AffiliatedTransport.transported
      (WeightedShift.fieldUnboundedMultiplier circleMeasure
        (fun x k => (Real.exp (b (action θ k x)) : ℂ))) p.range).starProjection ∈ algebra θ :=
  positive_orbit_transported_projection_mem θ (fun x => Real.exp (b x))
    (fun x => (Real.exp_pos (b x)).le) hb.exp p hp

end Invariant233.Rotation

end

end OAI
