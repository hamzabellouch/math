import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CentralCocycleHomology

namespace OAI

/-! # Coboundaries do not change the map on second homology -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {Q M : Type} [Group Q] [AddCommGroup M]

def groupOneCochainChains (b : Q → M) : (Q →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ b

theorem groupTwoCocycleChains_difference (c d : Q → Q → M) (b : Q → M)
    (he : ∀ q r, c q r = d q r + (b q + b r - b (q * r)))
    (z : (Q × Q) →₀ ℤ) :
    groupTwoCocycleChains c z = groupTwoCocycleChains d z +
      groupOneCochainChains b (groupHomology.d₂₁ (integralTrivialCoefficient Q) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]; abel
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [groupTwoCocycleChains_single, groupTwoCocycleChains_single, he,
      groupHomology.d₂₁_single]
    change n • (d q r + (b q + b r - b (q * r))) = n • d q r +
      groupOneCochainChains b
        (Finsupp.single r n - Finsupp.single (q * r) n + Finsupp.single q n)
    simp only [map_add, map_sub, groupOneCochainChains,
      Finsupp.linearCombination_single, smul_add, smul_sub]
    abel

theorem groupTwoCocycleHomology_eq_of_coboundary (c d : Q → Q → M)
    (hc : ∀ q r s, c q r + c (q * r) s = c r s + c q (r * s))
    (hd : ∀ q r s, d q r + d (q * r) s = d r s + d q (r * s))
    (b : Q → M) (he : ∀ q r, c q r = d q r + (b q + b r - b (q * r))) :
    groupTwoCocycleHomology c hc = groupTwoCocycleHomology d hd := by
  apply LinearMap.ext
  intro x
  induction x using groupHomology.H2_induction_on with
  | h z =>
    rw [groupTwoCocycleHomology_π, groupTwoCocycleHomology_π,
      groupTwoCocycleChains_difference c d b he, z.property, map_zero, add_zero]

end PolycyclicRecognition

end

end OAI
