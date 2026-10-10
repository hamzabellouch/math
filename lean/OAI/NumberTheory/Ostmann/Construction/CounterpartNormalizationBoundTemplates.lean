import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsTemplates

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.CounterpartNormalizationBound
open Arithmetic.HistoryProductWindows

def bulkCount (q : SourceSlot) : ℝ := if q.role=.bulk then 1 else 0

lemma bulkCount_add_fixedCount (q : SourceSlot) : bulkCount q+fixedCount q=1 := by
  unfold bulkCount fixedCount
  split_ifs <;> norm_num

lemma sourceSum_bulkCount_initial (m k : ℕ) :
    sourceSum bulkCount (Template.initial m k)=(m:ℝ) := by
  have hs : sourceSum bulkCount (Template.initial m k)+sourceSum fixedCount (Template.initial m k)=
      ((Template.initial m k).length:ℝ) := by
    rw [sourceSum,sourceSum,← List.sum_append]
    have he : ((Template.initial m k).map bulkCount).sum+
        ((Template.initial m k).map fixedCount).sum=
        ((Template.initial m k).map (fun q => bulkCount q+fixedCount q)).sum := by
      rw [List.sum_map_add]
    rw [List.sum_append,he]
    simp only [bulkCount_add_fixedCount,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one]
  rw [sourceSum_fixedCount_initial,InitialCoordinatesTemplate.initial_length] at hs
  push_cast at hs
  linarith

lemma sourceSum_bulkCount_remainder (T : List SourceSlot) (j : ℕ) :
    sourceSum bulkCount (Template.remainder j T)=sourceSum bulkCount T := by
  induction T with
  | nil => simp [Template.remainder,sourceSum]
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · have hb : q.role≠.bulk := by simp [hq]
      simpa [Template.remainder,sourceSum,hq,hb,bulkCount] using ih
    · simpa [Template.remainder,sourceSum,hq] using congrArg (fun t => bulkCount q+t) ih

lemma sourceSum_bulkCount_pruned (T : List SourceSlot) (l : ℕ) :
    sourceSum bulkCount (pruned T l)=sourceSum bulkCount T := by
  induction l with
  | zero => rfl
  | succ l ih => exact (sourceSum_bulkCount_remainder _ _).trans ih

theorem sourceSum_bulkCount_remaining (m k l : ℕ) :
    sourceSum bulkCount (Template.remainder (l+1) (Template.current (Template.initial m k) l))=
      (2:ℝ)^l*(m:ℝ) := by
  rw [sourceSum_bulkCount_remainder,sourceSum_current,sourceSum_bulkCount_pruned,
    sourceSum_bulkCount_initial]

lemma current_mem_seed {q : SourceSlot} {T : List SourceSlot} {l : ℕ}
    (hq : q∈Template.current T l) : q∈T := by
  induction l with
  | zero => exact hq
  | succ l ih =>
    have h : q∈Template.remainder (l+1) (Template.current T l) := by
      simpa only [Template.current,List.mem_append,or_self] using hq
    exact ih (List.mem_filter.mp h).1

theorem remaining_origin_metadata (m k l : ℕ) (q : SourceSlot)
    (hq : q∈Template.remainder (l+1) (Template.current (Template.initial m k) l)) :
    q.origin < m+6+4*k ∧ (q.role=.bulk ↔ q.origin < m) := by
  have hseed := current_mem_seed (List.mem_filter.mp hq).1
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hseed
  subst q
  refine ⟨?_,?_⟩
  · simpa only [InitialCoordinatesTemplate.initialRoles_length] using i.isLt
  · exact InitialCoordinatesTemplate.initialRoles_bulk_iff m k i

end Ostmann.Construction.CounterpartNormalizationBound

end

end OAI
