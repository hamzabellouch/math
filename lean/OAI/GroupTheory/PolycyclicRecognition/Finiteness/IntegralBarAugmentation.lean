import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBarNaturality

namespace OAI

/-! # Augmentation and degenerate bar chains -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear

def integralBarAugmentation (X : Type) : (X →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem integralBarAugmentation_single {X : Type} (x : X) (n : ℤ) :
    integralBarAugmentation X (Finsupp.single x n) = n := by
  simp [integralBarAugmentation]

variable {Q : Type} [Group Q]

theorem integralBarAugmentation_boundary (z : (Q × Q) →₀ ℤ) :
    integralBarAugmentation Q (groupHomology.d₂₁ (integralTrivialCoefficient Q) z) =
      integralBarAugmentation (Q × Q) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [groupHomology.d₂₁_single]
    change integralBarAugmentation Q
      (Finsupp.single r n - Finsupp.single (q * r) n + Finsupp.single q n) = _
    simp

theorem integralBarAugmentation_cycle (z : groupHomology.cycles₂
    (integralTrivialCoefficient Q)) : integralBarAugmentation (Q × Q) z.val = 0 := by
  rw [← integralBarAugmentation_boundary, z.property, map_zero]

def integralBarDegenerate : ((Q × Q) →₀ ℤ) →ₗ[ℤ] ((Q × Q) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (1, p.1 * p.2))

def integralBarDegeneratePrimitive : ((Q × Q) →₀ ℤ) →ₗ[ℤ] ((Q × Q × Q) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (1, 1, p.1 * p.2))

@[simp] theorem integralBarDegenerate_single (q r : Q) (n : ℤ) :
    integralBarDegenerate (Finsupp.single (q, r) n) = Finsupp.single (1, q * r) n := by
  simp [integralBarDegenerate]

theorem integralBarDegenerate_boundary (z : (Q × Q) →₀ ℤ) :
    groupHomology.d₃₂ (integralTrivialCoefficient Q) (integralBarDegeneratePrimitive z) =
      integralBarDegenerate z -
        Finsupp.single (1, 1) (integralBarAugmentation (Q × Q) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw, Finsupp.single_add]; abel
  | single p n =>
    rcases p with ⟨q, r⟩
    have hp : integralBarDegeneratePrimitive (Finsupp.single (q, r) n) =
        Finsupp.single (1, 1, q * r) n := by simp [integralBarDegeneratePrimitive]
    rw [hp, groupHomology.d₃₂_single, integralBarDegenerate_single,
      integralBarAugmentation_single]
    change Finsupp.single (1, q * r) n - Finsupp.single (1 * 1, q * r) n +
      Finsupp.single (1, 1 * (q * r)) n - Finsupp.single (1, 1) n = _
    simp

end PolycyclicRecognition

end

end OAI
