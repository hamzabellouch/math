import OAI.GameTheory.SnakyTwentyOne.Cards.Height21Part01
import OAI.GameTheory.SnakyTwentyOne.Certificate.Summary
import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game
import OAI.GameTheory.SnakyTwentyOne.Semantics.Geometry
import OAI.GameTheory.SnakyTwentyOne.Semantics.Policy
import OAI.GameTheory.SnakyTwentyOne.Semantics.Replies

namespace OAI

namespace SnakyPrototype
theorem empty_board_wins_21 : WinsIn HasSnaky 21 ∅ ∅ := by
  exact Certificate21.row_works_727 ∅ ∅ (by simp)
    (by simp [Certificate21.required_727]) (by simp)
end SnakyPrototype
namespace SnakyPrototype
open OrdinaryStrategy
theorem snaky_winning_strategy_21_with_legal_states :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k := by
  refine ⟨policy HasSnaky, policy_fresh HasSnaky, ?_⟩
  intro β hβ
  refine ⟨policy_wins (fun M N hMN hw => HasSnaky.mono hw hMN)
      21 β ∅ ∅ empty_board_wins_21 hβ, ?_, ?_, ?_⟩
  · simpa using playState_maker_card (policy HasSnaky) (policy_fresh HasSnaky)
      21 β ∅ ∅ 21
  · exact final_maker_disjoint (policy HasSnaky) (policy_fresh HasSnaky)
      20 β ∅ ∅ (by simp) hβ
  · intro k hk
    simpa using playState_legal_prefix (policy HasSnaky) (policy_fresh HasSnaky)
      21 β ∅ ∅ (by simp) hβ k hk
theorem snaky_winning_strategy_21 :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell,
        LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 := by
  obtain ⟨σ, hσ, hw⟩ := snaky_winning_strategy_21_with_legal_states
  exact ⟨σ, hσ, fun β hβ => (hw β hβ).1⟩
end SnakyPrototype

end OAI
