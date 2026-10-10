import OAI.Probability.SwitchChain.Definitions
import OAI.Probability.SwitchChain.MixingArithmetic

namespace OAI

noncomputable section
namespace Problem315

theorem stateCount_le_two_pow_square (n : ℕ) (d : Fin n → ℕ) :
    stateCount n d ≤ 2 ^ (n ^ 2) := by
  classical
  have hinj : Function.Injective (fun G : GraphState n d => G.val.Adj) := by
    intro G H h
    apply Subtype.ext
    apply SimpleGraph.ext
    exact h
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa [stateCount, allGraphStates, Fintype.card_fun, pow_mul, pow_two] using hcard

theorem mixedAt_polynomial_of_tv_estimate (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hTV : ∀ G : GraphState n d,
      tvDistanceFrom n d (2 * n ^ 8) G ≤
        Real.sqrt (stateCount n d : ℝ) / 2 *
          Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
            (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) :
    MixedAt n d (2 * n ^ 8) := by
  classical
  intro G
  exact (hTV G).trans (exponential_tv_bound_at_polynomial_time n
    (stateCount n d) hn (by simpa [pow_two] using stateCount_le_two_pow_square n d))

theorem exists_mixingTime_le_of_mixedAt (n : ℕ) (d : Fin n → ℕ) (t : ℕ)
    (ht : MixedAt n d t) :
    ∃ h : (∃ s : ℕ, MixedAt n d s), mixingTime n d h ≤ t := by
  classical
  refine ⟨⟨t, ht⟩, ?_⟩
  exact Nat.find_min' _ ht

theorem polynomial_mixing_of_tv_bound (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hTV : ∀ (t : ℕ) (G : GraphState n d),
      tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
        Real.exp (- (t : ℝ) /
          (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) :
    ∃ h : (∃ t : ℕ, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8 := by
  exact exists_mixingTime_le_of_mixedAt n d (2 * n ^ 8)
    (mixedAt_polynomial_of_tv_estimate n d hn (hTV (2 * n ^ 8)))

end Problem315

end

end OAI
