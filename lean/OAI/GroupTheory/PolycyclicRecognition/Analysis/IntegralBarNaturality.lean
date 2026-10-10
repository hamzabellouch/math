import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FirstHomologyAbelianizationNaturality

namespace OAI

/-! # Low-degree bar naturality with integral trivial coefficients -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G H : Type} [Group G] [Group H]

@[simp] theorem integralBarMap₁_single (f : G →* H) (g : G) (n : ℤ) :
    groupHomology.chainsMap₁ f (groupIntegralTrivialCoefficientMap f)
      (Finsupp.single g n) = Finsupp.single (f g) n := by
  simp [groupHomology.chainsMap₁, groupIntegralTrivialCoefficientMap]

@[simp] theorem integralBarMap₂_single (f : G →* H) (g h : G) (n : ℤ) :
    groupHomology.chainsMap₂ f (groupIntegralTrivialCoefficientMap f)
      (Finsupp.single (g, h) n) = Finsupp.single (f g, f h) n := by
  simp [groupHomology.chainsMap₂, groupIntegralTrivialCoefficientMap]

theorem integralBarMap_boundary (f : G →* H) (z : (G × G) →₀ ℤ) :
    groupHomology.d₂₁ (integralTrivialCoefficient H)
      (groupHomology.chainsMap₂ f (groupIntegralTrivialCoefficientMap f) z) =
    groupHomology.chainsMap₁ f (groupIntegralTrivialCoefficientMap f)
      (groupHomology.d₂₁ (integralTrivialCoefficient G) z) := by
  exact congrArg (fun k => k.hom z)
    (groupHomology.mapShortComplexH1 f (groupIntegralTrivialCoefficientMap f)).comm₁₂

end PolycyclicRecognition

end

end OAI
