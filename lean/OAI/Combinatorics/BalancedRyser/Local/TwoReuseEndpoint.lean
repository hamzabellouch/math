import OAI.Combinatorics.BalancedRyser.Results

namespace OAI

namespace Balanced.Local

open RootChildPartition UsedEventUnion Timing
open scoped BigOperators
noncomputable section
open scoped Classical
universe u

example :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
        ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        (∑ a : DirectionAssignment F b 2,
          if Eligible P a then offsetProbability (fun M =>
            Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
          ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
            (Fintype.card F : ℝ) ^ (4 * b) *
              (C * (b : ℝ) ^ 3 / Fintype.card F) :=
  Balanced.pencil_two_reuses

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

example [IsEmpty (DirectionToken b κ ↪ Direction F)]
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) :
    injectionAverage P bits p E = 0 := by
  simp [injectionAverage]

example (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (hc : c ∈ P.classSet ij.1) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) = 0 := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
  have hn : ¬ (∀ t, P.classOf ij.1 t ≠ c) := fun h => h j hj
  simp [injectionAverage, conditionedOffsetProbability, offsetProbability,
    usedConstituentTest, hn]

example (P : EqualityPattern b κ) : prefixTokens P ∅ = ∅ := by
  simp [prefixTokens]

example : (Finset.univ : Finset (DirectionToken b κ)).card ≤ 5*b :=
  card_token_set_le _

end
end Balanced.Local

end OAI
