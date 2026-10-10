import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesDefs
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSupport
import OAI.NumberTheory.Ostmann.Construction.ReorderNaturalityPlan

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport

theorem decoded_plan_eq (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (a b : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hcd : historyFrequencies sources seed V l c=historyFrequencies sources seed V l d)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside) :
    plan (decodeHistory sources seed V l a c) hc=plan (decodeHistory sources seed V l b d) hd := by
  induction l generalizing a b with
  | zero => change Plan.leaf a.frequency=Plan.leaf b.frequency; rw [hab]
  | succ l ih =>
    dsimp only [historyFrequencies] at hcd
    have hv : c.1=d.1 := congrArg (fun z : FrequencyChoices V (l+1) => z.1) hcd
    have hw : c.2.1=d.2.1 := congrArg (fun z => z.2.1) hcd
    have hl := congrArg (fun z => z.2.2.1) hcd
    have hr := congrArg (fun z => z.2.2.2) hcd
    have hca := decoded_children_match sources seed V l a c ha
    have hdb := decoded_children_match sources seed V l b d hb
    simp only [decodeHistory,History.nodeLeft,History.nodeRight,decodeHistory_root] at hca hdb
    have hsa := Template.matches_halves (Template.remainder (l+1) (Template.current seed l)) a.small ha
    have hsb := Template.matches_halves (Template.remainder (l+1) (Template.current seed l)) b.small hb
    have hua := assignedSlots_length sources (Template.extracted (l+1) (Template.current seed l)) c.2.2.1
    have hub := assignedSlots_length sources (Template.extracted (l+1) (Template.current seed l)) d.2.2.1
    have hsplitA := permutationOrder_eq_range (History.supported_small_split hc)
      (List.take_append_drop _ _).symm (supported_small_nodup hc)
    have hsplitB := permutationOrder_eq_range (History.supported_small_split hd)
      (List.take_append_drop _ _).symm (supported_small_nodup hd)
    have hleft := permutationOrder_reinsert_symm_eq hua (Template.matches_length hsa.1)
      hub (Template.matches_length hsb.1) (supported_left_concat_nodup hc) (supported_left_concat_nodup hd)
    have hright := permutationOrder_reinsert_symm_eq hua (Template.matches_length hsa.2)
      hub (Template.matches_length hsb.2) (supported_right_concat_nodup hc) (supported_right_concat_nodup hd)
    have hil := ih _ _ c.2.2.2.1 d.2.2.2.1 hca.1 hdb.1
      (congrArg Subtype.val hv) hl (History.supported_left hc) (History.supported_left hd)
    have hir := ih _ _ c.2.2.2.2 d.2.2.2.2 hca.2 hdb.2
      (congrArg Subtype.val hw) hr (History.supported_right hc) (History.supported_right hd)
    dsimp only [decodeHistory,plan]
    congr 1
    · simpa only [decodeHistory_root] using congrArg Subtype.val hv
    · simpa only [decodeHistory_root] using congrArg Subtype.val hw
    · exact (Template.matches_length hsa.1).trans (Template.matches_length hsb.1).symm
    · exact hsplitA.trans ((congrArg List.range ((Template.matches_length ha).trans
        (Template.matches_length hb).symm)).trans hsplitB.symm)
    · simpa only [decodeHistory_root] using hleft
    · simpa only [decodeHistory_root] using hright

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
