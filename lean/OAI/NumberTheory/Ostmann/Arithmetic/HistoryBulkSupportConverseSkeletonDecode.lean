import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeletonDecodeBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction

theorem rootStatic_decode_redraw (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    {outside : List ℕ} (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hf : a.frequency=b.frequency) (hbprime : b.PrimeSmall) :
    RootStatic V (decodeHistory sources seed V l b c) := by
  have hat : a.TemplateAt l := by
    simpa only [decodeHistory_root] using History.supported_template hs
  have hfn : b.frequency≠0 := by
    rw [←hf]
    simpa only [decodeHistory_root] using History.supported_root_frequency_ne_zero hs
  have hfb : b.frequency.natAbs≤V l := by
    rw [←hf]
    simpa only [decodeHistory_root] using History.supported_root_frequency_bound hs
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [decodeHistory_root] using hbprime
  · simpa only [decodeHistory_root] using templateAt_of_matches ha hb hat
  · simpa only [decodeHistory_root] using hfn
  · simpa only [decodeHistory_root] using hfb

theorem staticSkeleton_decode_redraw (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    {outside : List ℕ} (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hf : a.frequency=b.frequency) (hbprime : b.PrimeSmall) :
    StaticSkeleton V (decodeHistory sources seed V l b c) := by
  induction l generalizing a b with
  | zero => exact rootStatic_decode_redraw sources seed V 0 a b c ha hb hs hf hbprime
  | succ l ih =>
    let H := decodeHistory sources seed V (l+1) a c
    let K := decodeHistory sources seed V (l+1) b c
    let T := Template.current seed l
    let U := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    let n := (Template.remainder (l+1) T).length
    have hnewroot := rootStatic_decode_redraw sources seed V (l+1) a b c ha hb hs hf hbprime
    have hchild := decoded_children_small_perm sources seed V l b c (Template.matches_length hb)
    have holdmatches := decoded_children_match sources seed V l a c ha
    have hnewmatches := decoded_children_match sources seed V l b c hb
    have huprime : ∀q∈U,q.value.Prime := assignedSlots_prime sources _ c.2.2.1
    have huroles : ∀q∈U,q.role=.compensation (l+1) :=
      assignedSlots_extracted_roles sources T (l+1) c.2.2.1
    have hunodup : (U.map SmallSlot.value).Nodup :=
      compensation_values_nodup_of_supported hs
    have hlprime : (History.nodeLeft K).root.PrimeSmall :=
      child_primeSmall_of_perm hbprime huprime
        (fun q hq => List.mem_of_mem_take hq) hchild.1
    have hrprime : (History.nodeRight K).root.PrimeSmall :=
      child_primeSmall_of_perm hbprime huprime
        (fun q hq => List.mem_of_mem_drop hq) hchild.2
    have hlold := History.supported_left hs
    have hrold := History.supported_right hs
    have hl := ih (History.nodeLeft H).root (History.nodeLeft K).root c.2.2.2.1
      holdmatches.1 hnewmatches.1
      (by simpa only [H,decodeHistory,History.nodeLeft,decodeHistory_root] using hlold)
      (by simp only [H,K,decodeHistory,History.nodeLeft,decodeHistory_root]) hlprime
    have hr := ih (History.nodeRight H).root (History.nodeRight K).root c.2.2.2.2
      holdmatches.2 hnewmatches.2
      (by simpa only [H,decodeHistory,History.nodeRight,decodeHistory_root] using hrold)
      (by simp only [H,K,decodeHistory,History.nodeRight,decodeHistory_root]) hrprime
    change RootStatic V K ∧
      NodeStatic b U (b.small.take n) (b.small.drop n) (History.nodeLeft K) (History.nodeRight K) ∧
      StaticSkeleton V (History.nodeLeft K) ∧ StaticSkeleton V (History.nodeRight K)
    refine ⟨hnewroot,⟨huroles,?_,hchild.1,hchild.2,huprime,hunodup⟩,?_,?_⟩
    · simpa only [List.take_append_drop] using List.Perm.refl b.small
    · simpa only [K,decodeHistory,History.nodeLeft,decodeHistory_root] using hl
    · simpa only [K,decodeHistory,History.nodeRight,decodeHistory_root] using hr

theorem staticSkeleton_assigned_redraw (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (s : ℤ) (Gp Gm Gp' Gm' : ℕ) (c : HistoryChoices sources seed V l)
    {outside : List ℕ}
    (hs : (decodeHistory sources seed V l
      ⟨s,Gp,Gm,assignedSlots sources (Template.current seed l) x⟩ c).Supported V outside) :
    StaticSkeleton V (decodeHistory sources seed V l
      ⟨s,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩ c) :=
  staticSkeleton_decode_redraw sources seed V l _ _ c
    (Template.assignedSlots_matches sources _ x) (Template.assignedSlots_matches sources _ y)
    hs rfl (assignedSlots_prime sources _ y)

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
