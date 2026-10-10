import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion HistoryLinearization

theorem decodeHistory_bulkValues (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources (Template.initial m k) V l)
    (ha : Template.Matches (Template.current (Template.initial m k) l) a.small)
    (path : Tree.Leaves l) :
    bulkValues (leafStateAt (decodeHistory sources (Template.initial m k) V l a c) path).small=
      bulkBlock m l path (bulkValues a.small) := by
  induction l generalizing a with
  | zero => rfl
  | succ l ih =>
    let T := Template.current (Template.initial m k) l
    let n := (Template.remainder (l+1) T).length
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    have hh := Template.matches_halves (Template.remainder (l+1) T) a.small ha
    have hu := Template.assignedSlots_matches sources (Template.extracted (l+1) T) c.2.2.1
    have hn : (bulkValues (a.small.take n)).length=2^l*m :=
      (bulkValues_length_of_matches hh.1).trans (remainder_count_bulk m k l)
    have hb := bulkValues_halves a.small n (2^l*m) hn
    simp only [decodeHistory,leafStateAt,bulkBlock]
    split_ifs with hp
    · rw [ih _ c.2.2.2.2 (Template.reinsert_matches _ _ _ _ hu hh.2)]
      change bulkBlock m l (Fin.tail path) (bulkValues (Template.reinsert (l+1) T u
        (a.small.drop n))) = _
      rw [bulkValues_reinsert _ _ _ _ hu hh.2,hb.2]
    · rw [ih _ c.2.2.2.1 (Template.reinsert_matches _ _ _ _ hu hh.1)]
      change bulkBlock m l (Fin.tail path) (bulkValues (Template.reinsert (l+1) T u
        (a.small.take n))) = _
      rw [bulkValues_reinsert _ _ _ _ hu hh.1,hb.1]

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
