import OAI.Analysis.MutuallyUnbiased.Cubic.CubicPrelim
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicMultiplicityCore

namespace OAI

/-! Full one-value or three-and-three dichotomy for cubed entries. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The cubed coordinates either have one common value, or have exactly two
values occurring three times each; each three-coordinate group sums to zero. -/
theorem cube_values_dichotomy (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    (∀ i, v i ^ 3 = v 0 ^ 3) ∨
      ∃ b : ℂ, v 0 ^ 3 ≠ b ∧
        (∀ i, v i ^ 3 = v 0 ^ 3 ∨ v i ^ 3 = b) ∧
        (cubeClass v (v 0 ^ 3)).card = 3 ∧ (cubeClass v b).card = 3 ∧
        (∑ i ∈ cubeClass v (v 0 ^ 3), v i) = 0 ∧
        (∑ i ∈ cubeClass v b, v i) = 0 := by
  classical
  by_cases h : ∀ i, v i ^ 3 = v 0 ^ 3
  · exact Or.inl h
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hab := Ne.symm hj
    have hvalues : ∀ i, v i ^ 3 = v 0 ^ 3 ∨ v i ^ 3 = v j ^ 3 := fun i =>
      quadratic_two_values
        (cubed_entry_quadratic v hv h1 h2 0)
        (cubed_entry_quadratic v hv h1 h2 j)
        (cubed_entry_quadratic v hv h1 h2 i) hab
    have hc := two_cube_classes_card_three v hv h1 h2 (v 0 ^ 3) (v j ^ 3)
      hab hvalues 0 j rfl rfl
    exact Or.inr ⟨v j ^ 3, hab, hvalues, hc⟩

end MUB6

end

end OAI
