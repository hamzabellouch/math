import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralBarLift
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegralBarAugmentation

namespace OAI

/-! # Projection of the corrected central bar lift -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q)

theorem centralBarKernelLetters_augmentation (σ : E.Section) (z : (Q × Q) →₀ ℤ) :
    integralBarAugmentation N (centralBarKernelLetters E σ z) =
      integralBarAugmentation (Q × Q) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [centralBarKernelLetters_single, integralBarAugmentation_single,
      integralBarAugmentation_single]

theorem centralBarLift_projection (σ : E.Section) (z : (Q × Q) →₀ ℤ) :
    groupHomology.chainsMap₂ E.rightHom (groupIntegralTrivialCoefficientMap E.rightHom)
      (centralBarLift E σ z) = z - integralBarDegenerate z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]; abel
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [centralBarLift_single, map_sub, integralBarMap₂_single,
      integralBarMap₂_single, σ.rightHom_section, σ.rightHom_section,
      σ.rightHom_section, E.rightHom_inl, integralBarDegenerate_single]

theorem centralKernelBar_projection (z : (N × N) →₀ ℤ) :
    groupHomology.chainsMap₂ E.rightHom (groupIntegralTrivialCoefficientMap E.rightHom)
      (groupHomology.chainsMap₂ E.inl (groupIntegralTrivialCoefficientMap E.inl) z) =
      Finsupp.single (1, 1) (integralBarAugmentation (N × N) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw, Finsupp.single_add]
  | single p n =>
    rcases p with ⟨a, b⟩
    rw [integralBarMap₂_single, integralBarMap₂_single, E.rightHom_inl,
      E.rightHom_inl, integralBarAugmentation_single]

end PolycyclicRecognition

end

end OAI
