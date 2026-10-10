import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsNominal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationMetadata
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesPair
import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBoundPriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationNormalizationBudget
open Construction CanonicalOccurrenceTransport InitialCoordinatesTemplate HistoryProductWindows

theorem extracted_initial_length (m k j : ℕ) :
    (Template.extracted j (Template.initial m k)).length =
      if 0<j ∧ j≤k then 4 else 0 := by
  induction k with
  | zero =>
    rw [initial_zero]
    simp only [Template.extracted,List.filter_append]
    change (Template.extracted j (sourceBlock 0 m .bulk) ++
      Template.extracted j (sourceBlock m 6 .top)).length = _
    rw [extracted_sourceBlock,extracted_sourceBlock]
    simp
    omega
  | succ k ih =>
    rw [initial_succ]
    simp only [Template.extracted,List.filter_append,List.length_append]
    change (Template.extracted j (Template.initial m k)).length+
      (Template.extracted j (sourceBlock (m+6+4*k) 4 (.compensation (k+1)))).length = _
    rw [ih,extracted_sourceBlock]
    simp only [SlotRole.compensation.injEq]
    split_ifs <;> simp_all [sourceBlock] <;> omega

theorem extracted_current_length (m k l : ℕ) (hl : l<k) :
    (Template.extracted (l+1) (Template.current (Template.initial m k) l)).length = 2^l*4 := by
  change Template.countRole (Template.current (Template.initial m k) l) (.compensation (l+1)) = _
  rw [Template.countRole_current]
  · change 2^l*(Template.extracted (l+1) (Template.initial m k)).length = _
    simp [extracted_initial_length, show 0 < l+1 ∧ l+1 ≤ k by omega]
  · intro j hj hjl he
    have := SlotRole.compensation.inj he
    omega

theorem paired_internal_card (m k l : ℕ) (hl : l≤k) :
    Fintype.card (Internal (Template.initial m k) l ⊕ Internal (Template.initial m k) l) =
      4*l*2^l := by
  have hsingle : 2*Fintype.card (Internal (Template.initial m k) l)=4*l*2^l := by
    induction l with
    | zero => simp [Internal]
    | succ l ih =>
      have hi := ih (by omega)
      change 2*(Fintype.card
        (Fin (Template.extracted (l+1) (Template.current (Template.initial m k) l)).length ⊕
          (Internal (Template.initial m k) l ⊕ Internal (Template.initial m k) l))) = _
      rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_sum,extracted_current_length m k l (by omega)]
      rw [pow_succ]
      nlinarith
  simpa only [Fintype.card_sum,two_mul] using hsingle

theorem internalSource_compensation (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    ∃j : ℕ,(internalSource seed i).role=.compensation j := by
  induction l with
  | zero => exact Empty.elim i
  | succ l ih =>
    rcases i with i | i | i
    · refine ⟨l+1,?_⟩
      have hm := List.get_mem (Template.extracted (l+1) (Template.current seed l)) i
      exact of_decide_eq_true (List.mem_filter.mp hm).2
    · exact ih i
    · exact ih i

theorem internalSource_origin_metadata (m k l : ℕ) (i : Internal (Template.initial m k) l) :
    (internalSource (Template.initial m k) i).origin < m+6+4*k ∧
    (internalSource (Template.initial m k) i).role≠.bulk ∧
    ((internalSource (Template.initial m k) i).role=.bulk ↔
      (internalSource (Template.initial m k) i).origin < m) := by
  have hm := HistoryRepresentativeSourceSeparation.internalSource_mem_seed (Template.initial m k) i
  obtain ⟨a,ha⟩ := List.mem_ofFn.mp hm
  have hrole := InitialCoordinatesTemplate.initialRoles_bulk_iff m k a
  obtain ⟨j,hj⟩ := internalSource_compensation (Template.initial m k) i
  refine ⟨?_,?_,?_⟩
  · rw [←ha]
    simpa only [initialRoles_length] using a.isLt
  · rw [hj]
    exact SlotRole.noConfusion
  · rw [←ha]
    exact hrole

end Ostmann.Arithmetic.HistoryCompensationNormalizationBudget

end

end OAI
