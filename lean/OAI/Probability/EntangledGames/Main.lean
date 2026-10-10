import OAI.Probability.EntangledGames.StrategyBridge

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder
namespace ThresholdParallelRepetition

theorem threshold_parallel_repetition :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x y a b : ℕ) (G : Game x y a b), entangledValue G < 1 →
      ∀ (δ : ℝ), 0 < δ → δ < 1 - entangledValue G →
      ∀ (k : ℕ), 1 ≤ k →
        (∀ S : RepeatedStrategy x y a b k,
          thresholdProbability G δ S ≤
            Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)) ∧
        thresholdValue (k := k) G δ ≤
          Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k) := by
  refine ⟨((2:ℝ)^101)⁻¹, by positivity, ?_⟩
  intro x y a b G _ δ hδ hδv k hk
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hs : entangledValue G+δ ≤ 1 := by linarith
  have hstrategy : ∀ S : RepeatedStrategy x y a b k,
      thresholdProbability G δ S ≤
        Real.exp (-((2:ℝ)^101)⁻¹ * δ^13 / (1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))*k) := by
    intro S
    rw [S.threshold_eq_model G (by omega) δ]
    have hh := (S.repetitionModel G).threshold_exp_bound G rfl rfl hδ hs
    simp only [Fintype.card_fin] at hh
    refine hh.trans_eq ?_
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨hstrategy, ?_⟩
  unfold thresholdValue
  apply csSup_le
  · let S : RepeatedStrategy x y a b k := Strategy.deterministic (fun _ => 0) (fun _ => 0)
    exact ⟨_, Set.mem_range_self S⟩
  · rintro _ ⟨S,rfl⟩
    exact hstrategy S

end ThresholdParallelRepetition

end

end OAI
