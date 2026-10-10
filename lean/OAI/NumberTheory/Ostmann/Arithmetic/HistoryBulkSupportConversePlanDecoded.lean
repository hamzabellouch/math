import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanReinsert

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction CanonicalOccurrenceTransport

theorem decoded_reference_plan_fits (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency = b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    Fits (plan (decodeHistory sources seed V l a c) hs)
      (decodeHistory sources seed V l b c) := by
  induction l generalizing a b with
  | zero => exact hab
  | succ l ih =>
    have hca := decoded_children_match sources seed V l a c ha
    have hcb := decoded_children_match sources seed V l b c hb
    simp only [decodeHistory,History.nodeLeft,History.nodeRight,decodeHistory_root] at hca hcb
    have hsa := Template.matches_halves (Template.remainder (l+1) (Template.current seed l)) a.small ha
    have hsb := Template.matches_halves (Template.remainder (l+1) (Template.current seed l)) b.small hb
    have hu := assignedSlots_length sources (Template.extracted (l+1) (Template.current seed l)) c.2.2.1
    have hsplit := permutationOrder_eq_range (History.supported_small_split hs)
      (List.take_append_drop _ _).symm (supported_small_nodup hs)
    have hleft := select_reinsert_map_of_same_lengths (l+1) (Template.current seed l)
      _ _ _ _ hu (Template.matches_length hsa.1) hu (Template.matches_length hsb.1)
      (supported_left_concat_nodup hs) (fun q => (q.value:ℚ)) 0
    have hright := select_reinsert_map_of_same_lengths (l+1) (Template.current seed l)
      _ _ _ _ hu (Template.matches_length hsa.2) hu (Template.matches_length hsb.2)
      (supported_right_concat_nodup hs) (fun q => (q.value:ℚ)) 0
    dsimp only [decodeHistory,plan,Fits]
    refine ⟨hab,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp only [decodeHistory_root]
    · simp only [decodeHistory_root]
    · exact (Template.matches_length hsa.1).trans (Template.matches_length hsb.1).symm
    · have hlen : a.small.length = (b.small.map (fun q => (q.value:ℚ))).length := by
        simpa only [List.length_map] using
          (Template.matches_length ha).trans (Template.matches_length hb).symm
      rw [hsplit,hlen,select_range,List.take_append_drop]
    · simpa only [decodeHistory_root] using hleft
    · simpa only [decodeHistory_root] using hright
    · apply ih _ _ c.2.2.2.1
      · exact hca.1
      · exact hcb.1
      · rfl
    · apply ih _ _ c.2.2.2.2
      · exact hca.2
      · exact hcb.2
      · rfl

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
