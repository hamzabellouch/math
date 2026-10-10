import OAI.Analysis.IrrationalRotation.Model.RotationTransfer
import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Analysis.FieldMultiplierAdjoint

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.Rotation

theorem mem_exponentialTransfer_domain_iff (θ : ℝ) (b : Circle → ℝ) (ξ : Hilbert) :
    ξ ∈ (exponentialTransfer θ b).domain ↔
      ∃ η : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
        η x k = (Real.exp (b (action θ k x)) : ℂ) * ξ x k :=
  WeightedShift.mem_fieldUnboundedMultiplier_domain_iff _ _

theorem exponentialTransfer_apply_ae (θ : ℝ) (b : Circle → ℝ)
    (ξ : (exponentialTransfer θ b).domain) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      exponentialTransfer θ b ξ x k = (Real.exp (b (action θ k x)) : ℂ) * ξ.val x k :=
  WeightedShift.fieldUnboundedMultiplier_apply_ae _ _

theorem exponentialTransfer_injective (θ : ℝ) (b : Circle → ℝ) :
    Function.Injective (exponentialTransfer θ b) := by
  apply WeightedShift.fieldUnboundedMultiplier_injective
  exact Eventually.of_forall fun x k => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem exponentialTransfer_coefficient_measurable (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) (k : ℤ) :
    Measurable (fun x => Real.exp (b (action θ k x))) :=
  (hb.comp (action_continuous θ k).measurable).exp

theorem dense_exponentialTransfer_domain (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) : Dense ((exponentialTransfer θ b).domain : Set Hilbert) := by
  apply WeightedShift.dense_fieldUnboundedMultiplier_domain
  intro k
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable
    (exponentialTransfer_coefficient_measurable θ hb k).aestronglyMeasurable

theorem exponentialTransfer_selfAdjoint (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) : IsSelfAdjoint (exponentialTransfer θ b) := by
  apply WeightedShift.isSelfAdjoint_fieldUnboundedMultiplier_real
  intro k
  exact (exponentialTransfer_coefficient_measurable θ hb k).aestronglyMeasurable

theorem exponentialTransfer_isClosed (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) : (exponentialTransfer θ b).IsClosed :=
  (exponentialTransfer_selfAdjoint θ hb).isClosed

theorem exponentialTransfer_nonnegative (θ : ℝ) (b : Circle → ℝ)
    (ξ : (exponentialTransfer θ b).domain) :
    0 ≤ (inner ℂ ξ.val (exponentialTransfer θ b ξ)).re :=
  WeightedShift.fieldUnboundedMultiplier_nonnegative
    (fun x k => Real.exp (b (action θ k x)))
    (Eventually.of_forall fun _ _ => (Real.exp_pos _).le) ξ

end Invariant233.Rotation

end

end OAI
