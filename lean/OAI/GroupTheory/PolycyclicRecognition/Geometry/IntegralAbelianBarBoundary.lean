import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBarNaturality

namespace OAI

/-! # Filling one-chains in an abelian group

A finite integral one-chain with zero sum in the group is an actual bar
boundary. This is the degree-one comparison, with the primitive retained.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def abelianBarSum : (A →₀ ℤ) →ₗ[ℤ] Additive A :=
  Finsupp.linearCombination ℤ Additive.ofMul

theorem integralH1AbelianizationEquiv_abelian_chain (z : A →₀ ℤ) :
    integralH1AbelianizationEquiv
      (groupHomology.H1π (integralTrivialCoefficient A)
        ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient A)).inv z)) =
      (Abelianization.of : A →* Abelianization A).toAdditive.toIntLinearMap
        (abelianBarSum z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single a n =>
    rw [integralH1AbelianizationEquiv_single]
    simp only [abelianBarSum, Finsupp.linearCombination_single, map_smul]
    rfl

theorem abelianBar_boundary_of_sum_zero (z : A →₀ ℤ) (hz : abelianBarSum z = 0) :
    ∃ b : (A × A) →₀ ℤ, groupHomology.d₂₁ (integralTrivialCoefficient A) b = z := by
  have he : groupHomology.H1π (integralTrivialCoefficient A)
      ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient A)).inv z) = 0 := by
    apply integralH1AbelianizationEquiv.injective
    rw [integralH1AbelianizationEquiv_abelian_chain, hz, map_zero, map_zero]
  exact (groupHomology.H1π_eq_zero_iff _).mp he

end PolycyclicRecognition

end

end OAI
