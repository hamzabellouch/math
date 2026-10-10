import OAI.NumberTheory.TwoPoint.Bounds.RunSegments
import OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! Actual constant-run compression of a perfect block. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

/-- The decoder's greedy run heads are exactly the library's constant-run
compression, so its sublist and adjacent-inequality properties apply. -/
theorem destutter'_eq_columnRunHeads (a : α) (l : List α) :
    l.destutter' (· ≠ ·) a = a :: columnRunHeads (l.map some) (some a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b rest ih =>
      by_cases h : a = b
      · subst b
        simpa [List.destutter', columnRunHeads] using ih a
      · simpa [List.destutter', columnRunHeads, h] using congrArg (List.cons a) (ih b)

theorem columnRunHeads_eq_destutter (l : List α) :
    columnRunHeads (l.map some) none = l.destutter (· ≠ ·) := by
  cases l with
  | nil => rfl
  | cons a rest =>
      rw [List.destutter_cons', destutter'_eq_columnRunHeads]
      simp [columnRunHeads]

omit [DecidableEq α] in
/-- A subsequence with unequal adjacent entries has no repeated label when
all occurrences in the original block are interval-shaped. -/
theorem sublist_chain_nodup_of_intervals (l runs : List α) (hsub : runs.Sublist l)
    (hchain : runs.IsChain (· ≠ ·))
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) : runs.Nodup := by
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  have hchange : ∀ i j : Fin runs.length, i.val + 1 = j.val → l.get (e i) ≠ l.get (e j) := by
    intro i j hij
    rw [← he i, ← he j]
    have hj : i.val + 1 < runs.length := by omega
    have hc := (List.isChain_iff_getElem.mp hchain) i.val hj
    simpa only [List.get_eq_getElem, hij] using hc
  have hinj := run_labels_injective l.get hinterval e e.strictMono hchange
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  apply hinj
  change l.get (e i) = l.get (e j)
  rw [← he i, ← he j, hij]

/-- Each numerical label contributes at most one compressed run in a
perfect block. This is proved for the actual run-head algorithm. -/
theorem columnRunHeads_nodup (l : List α)
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    (columnRunHeads (l.map some) none).Nodup := by
  rw [columnRunHeads_eq_destutter]
  exact sublist_chain_nodup_of_intervals l _ (List.destutter_sublist (R := (· ≠ ·)) l)
    (List.isChain_destutter (R := (· ≠ ·)) l) hinterval

end TwoPointCorrelations

end OAI
