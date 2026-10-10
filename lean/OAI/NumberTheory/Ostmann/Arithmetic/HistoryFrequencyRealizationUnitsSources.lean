import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationUnitsDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts

theorem sourceMass_value_prime {sources : SourceFamily} {q : SmallSlot}
    (hq : sourceMass sources q≠0) : q.value.Prime := by
  unfold sourceMass at hq
  split_ifs at hq with hmem
  · exact (sources q.origin).prime q.value hmem
  · exact (hq rfl).elim

theorem source_slots_product_coprime (sources : SourceFamily) (R : ℕ)
    (hsource : ∀q,sourceMass sources q≠0 → Nat.Coprime q.value R)
    (xs : List SmallSlot) (hxs : ∀q∈xs,sourceMass sources q≠0) :
    Nat.Coprime (xs.map SmallSlot.value).prod R := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hsource q (hxs q hq)

theorem source_bulkProduct_coprime (sources : SourceFamily) (R : ℕ)
    (hsource : ∀q,sourceMass sources q≠0 → Nat.Coprime q.value R)
    (xs : List SmallSlot) (hxs : ∀q∈xs,sourceMass sources q≠0) :
    Nat.Coprime (bulkProduct xs) R :=
  source_slots_product_coprime sources R hsource _ (fun q hq=>hxs q (List.mem_filter.mp hq).1)

theorem decoded_frequencyUnits_of_source (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (R : ℕ)
    (hsource : ∀q,sourceMass sources q≠0 → Nat.Coprime q.value R)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hroot : ∀q∈a.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0) :
    FrequencyUnits R (decodeHistory sources seed V l a c) := by
  induction l generalizing a with
  | zero => exact source_bulkProduct_coprime sources R hsource a.small hroot
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
    have hl := ih (History.nodeLeft H).root c.2.2.2.1 hmatches.1 hlmass hleftmass
    have hr := ih (History.nodeRight H).root c.2.2.2.2 hmatches.2 hrmass hrightmass
    change Nat.Coprime (bulkProduct a.small) R ∧ Nat.Coprime (U.map SmallSlot.value).prod R ∧
      FrequencyUnits R (History.nodeLeft H) ∧ FrequencyUnits R (History.nodeRight H)
    refine ⟨source_bulkProduct_coprime sources R hsource a.small hroot,
      source_slots_product_coprime sources R hsource U hu,?_,?_⟩
    · simpa only [H,decodeHistory,History.nodeLeft,decodeHistory_root] using hl
    · simpa only [H,decodeHistory,History.nodeRight,decodeHistory_root] using hr

theorem FrequencyUnits.pow {R : ℕ} {l : ℕ} {h : History l}
    (hh : FrequencyUnits R h) (n : ℕ) : FrequencyUnits (R^n) h := by
  induction h with
  | leaf a => exact hh.pow_right n
  | node a p comp hp hm left right ihl ihr =>
    exact ⟨hh.1.pow_right n,hh.2.1.pow_right n,ihl hh.2.2.1,ihr hh.2.2.2⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
