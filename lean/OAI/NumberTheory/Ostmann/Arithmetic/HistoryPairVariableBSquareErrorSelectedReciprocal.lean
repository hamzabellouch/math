import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedSourceAtomBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairRows Conclusion Filter

theorem selected_decoded_reciprocal_sum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (V : ℕ → ℕ) (a b : State) (c e : HistoryChoices C.sources seed V l),
      Template.Matches (Template.current seed l) a.small →
      Template.Matches (Template.current seed l) b.small →
      choicesMass C.sources seed V l c ≠ 0 →
      choicesMass C.sources seed V l e ≠ 0 →
      (∑ i : Occurrences (decodeHistory C.sources seed V l a c)
          (decodeHistory C.sources seed V l b e),
        (1:ℝ)/(slot (decodeHistory C.sources seed V l a c)
          (decodeHistory C.sources seed V l b e) i).value) ≤
        (4*k*2^k:ℕ)*Real.exp (-Real.exp ((39/10000:ℝ)*L)) := by
  filter_upwards [HistorySelectedSourceAtomBounds.selected_source_atom_bounds_eventually
    d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro V a b c e ha hb' hc he
  have hsource := (hL E C hG hGu hcl hcu hb hd).2.1
  have h := decoded_pair_reciprocal_sum_le C.sources _ V l a b c e ha hb' hc he
    (Real.exp (-Real.exp ((39/10000:ℝ)*L))) (by
      intro origin p hp
      exact reciprocal_le_exp_neg_of_log_lower
        (by exact_mod_cast ((C.sources origin).prime p.val p.property).pos)
        (hsource origin p hp))
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact_mod_cast paired_initial_occurrence_count_le (2*(bulkSize k L/2)) k l hl

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
