import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionBasic
import OAI.NumberTheory.Ostmann.Construction.CanonicalLabels
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBoundsFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySupportReduction
open Construction

theorem decoded_largePrimes (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hroot : ∀q∈a.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j)) :
    LargePrimes V (decodeHistory sources seed V l a c) := by
  induction l generalizing a with
  | zero =>
    intro q hq
    exact sourceMass_value_gt (hfreq 0 le_rfl) (hroot q hq)
  | succ l ih =>
    let H := decodeHistory sources seed V (l+1) a c
    let U := assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) c.2.2.1
    have hc' :
        (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mass c.2.2.1 *
        choicesMass sources seed V l c.2.2.2.1 * choicesMass sources seed V l c.2.2.2.2≠0 := hc
    have hUmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc').1).1
    have hleftmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc').1).2
    have hrightmass := (mul_ne_zero_iff.mp hc').2
    have hu : ∀q∈U,sourceMass sources q≠0 :=
      assignedSlots_source_mass_ne_zero sources _ c.2.2.1 hUmass
    have hchild := decoded_children_small_perm sources seed V l a c (Template.matches_length ha)
    have hmatches := decoded_children_match sources seed V l a c ha
    have hlmass : ∀q∈(History.nodeLeft H).root.small,sourceMass sources q≠0 := by
      intro q hq
      have hq' := hchild.1.mem_iff.mp hq
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact hu q hq'
      · exact hroot q (List.mem_of_mem_take hq')
    have hrmass : ∀q∈(History.nodeRight H).root.small,sourceMass sources q≠0 := by
      intro q hq
      have hq' := hchild.2.mem_iff.mp hq
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact hu q hq'
      · exact hroot q (List.mem_of_mem_drop hq')
    have hfreq' : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j) :=
      fun j hj => hfreq j (by omega)
    have hl := ih (History.nodeLeft H).root c.2.2.2.1 hmatches.1 hlmass hleftmass hfreq'
    have hr := ih (History.nodeRight H).root c.2.2.2.2 hmatches.2 hrmass hrightmass hfreq'
    change (∀q∈a.small,V (l+1)<q.value) ∧ (∀q∈U,V (l+1)<q.value) ∧
      LargePrimes V (History.nodeLeft H) ∧ LargePrimes V (History.nodeRight H)
    refine ⟨fun q hq => sourceMass_value_gt (hfreq (l+1) le_rfl) (hroot q hq),
      fun q hq => sourceMass_value_gt (hfreq (l+1) le_rfl) (hu q hq),?_,?_⟩
    · simpa only [H,decodeHistory,History.nodeLeft,decodeHistory_root] using hl
    · simpa only [H,decodeHistory,History.nodeRight,decodeHistory_root] using hr

end Ostmann.Arithmetic.HistorySupportReduction

end

end OAI
