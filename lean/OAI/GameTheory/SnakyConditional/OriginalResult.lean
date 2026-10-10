import OAI.GameTheory.SnakyConditional.Opening.Opening
import OAI.GameTheory.SnakyConditional.Semantics.Policy

namespace OAI

namespace SnakyConditional
open OrdinaryStrategy
theorem snaky_winning_strategy :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell,
        LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 := by
  exact winsIn_has_ordinary_policy
    (fun M N hMN hw => HasSnaky.mono hw hMN) empty_board_wins
theorem snaky_winning_strategy_with_legal_states :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 ∧
        (playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (playState σ 35 β ∅ ∅ 35).1 (playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (playState σ 35 β ∅ ∅ k).1 (playState σ 35 β ∅ ∅ k).2 ∧
          (playState σ 35 β ∅ ∅ k).2.card = k := by
  refine ⟨policy HasSnaky, policy_fresh HasSnaky, ?_⟩
  intro β hβ
  refine ⟨policy_wins (fun M N hMN hw => HasSnaky.mono hw hMN)
      35 β ∅ ∅ empty_board_wins hβ, ?_, ?_, ?_⟩
  · simpa using playState_maker_card (policy HasSnaky) (policy_fresh HasSnaky)
      35 β ∅ ∅ 35
  · exact final_maker_disjoint (policy HasSnaky) (policy_fresh HasSnaky)
      34 β ∅ ∅ (by simp) hβ
  · intro k hk
    simpa using playState_legal_prefix (policy HasSnaky) (policy_fresh HasSnaky)
      35 β ∅ ∅ (by simp) hβ k hk
end SnakyConditional

end OAI
