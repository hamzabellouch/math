import OAI.NumberTheory.TwoPoint.Bounds.RunTransitionPaths
import OAI.NumberTheory.TwoPoint.Bounds.CompressedRuns
import OAI.NumberTheory.TwoPoint.Bounds.RunPartitionProperties
import Mathlib.Data.List.Range

namespace OAI

/-! Indexed run starts retain the constant intervals needed for quotient paths. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [DecidableEq α]

def IndexedRunStep (label : ℕ → α) (a b : ℕ × α) : Prop :=
  a.1 < b.1 ∧ label a.1 = a.2 ∧ label b.1 = b.2 ∧ a.2 ≠ b.2 ∧
    ∀ t ∈ Ico a.1 b.1, label t = a.2

/-- The scan retains the complete constant interval between consecutive
run starts, not just the unequal labels. -/
theorem scanRunTransitions_chain (label : ℕ → α) (a n len : ℕ) (i : α)
    (han : a < n) (hcurrent : label a = i)
    (hconst : ∀ t ∈ Ico a n, label t = i) :
    ((a, i) :: scanRunTransitions label n len i).IsChain (IndexedRunStep label) := by
  induction len generalizing a n i with
  | zero => exact .singleton _
  | succ len ih =>
      by_cases heq : label n = i
      · rw [scanRunTransitions, ite_eq_left heq]
        apply ih a (n + 1) i (by omega) hcurrent
        intro t ht
        rcases mem_Ico.mp ht with ⟨hat, htn⟩
        by_cases htn' : t < n
        · exact hconst t (mem_Ico.mpr ⟨hat, htn'⟩)
        · have he : t = n := by omega
          simpa only [he] using heq
      · rw [scanRunTransitions, ite_eq_right heq]
        apply List.IsChain.cons_cons
        · exact ⟨han, hcurrent, rfl, Ne.symm heq, hconst⟩
        · apply ih n (n + 1) (label n) (by omega) rfl
          intro t ht
          have he : t = n := by have := mem_Ico.mp ht; omega
          simp only [he]

/-- Labels in a scan agree with the actual numerical positions they record. -/
theorem scanRunTransitions_mem (label : ℕ → α) (n len : ℕ) (previous : α)
    (p : ℕ × α) (hp : p ∈ scanRunTransitions label n len previous) :
    n ≤ p.1 ∧ p.1 < n + len ∧ label p.1 = p.2 := by
  induction len generalizing n previous with
  | zero => simp [scanRunTransitions] at hp
  | succ len ih =>
      by_cases heq : label n = previous
      · rw [scanRunTransitions, ite_eq_left heq] at hp
        obtain ⟨hl, hu, he⟩ := ih (n + 1) previous hp
        exact ⟨by omega, by omega, he⟩
      · rw [scanRunTransitions, ite_eq_right heq, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨le_rfl, by omega, rfl⟩
        · obtain ⟨hl, hu, he⟩ := ih (n + 1) (label n) hp
          exact ⟨by omega, by omega, he⟩

def indexedBlockRuns (label : ℕ → α) (start len : ℕ) : List (ℕ × α) :=
  match len with
  | 0 => []
  | len + 1 => (start, label start) :: scanRunTransitions label (start + 1) len (label start)

theorem indexedBlockRuns_chain (label : ℕ → α) (start len : ℕ) :
    (indexedBlockRuns label start len).IsChain (IndexedRunStep label) := by
  cases len with
  | zero => exact .nil
  | succ len =>
      apply scanRunTransitions_chain label start (start + 1) len (label start) (by omega) rfl
      intro t ht
      have he : t = start := by have := mem_Ico.mp ht; omega
      simp only [he]

theorem indexedBlockRuns_mem (label : ℕ → α) (start len : ℕ) (p : ℕ × α)
    (hp : p ∈ indexedBlockRuns label start len) :
    start ≤ p.1 ∧ p.1 < start + len ∧ label p.1 = p.2 := by
  cases len with
  | zero => simp [indexedBlockRuns] at hp
  | succ len =>
      simp only [indexedBlockRuns, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨le_rfl, by omega, rfl⟩
      · obtain ⟨hl, hu, he⟩ := scanRunTransitions_mem label (start + 1) len (label start) p hp
        exact ⟨by omega, by omega, he⟩

def blockLabelList (label : ℕ → α) (start len : ℕ) : List α :=
  (List.range len).map (fun j => label (start + j))

omit [DecidableEq α] in
lemma blockLabelList_succ (label : ℕ → α) (start len : ℕ) :
    blockLabelList label start (len + 1) = label start :: blockLabelList label (start + 1) len := by
  simp only [blockLabelList, List.range_succ_eq_map, List.map_cons, Nat.add_zero,
    List.map_map, Function.comp_def]
  congr 2
  funext j
  congr 1
  omega

lemma scanRunTransitions_labels (label : ℕ → α) (n len : ℕ) (previous : α) :
    (scanRunTransitions label n len previous).map Prod.snd =
      columnRunHeads ((blockLabelList label n len).map some) (some previous) := by
  induction len generalizing n previous with
  | zero => rfl
  | succ len ih =>
      rw [blockLabelList_succ]
      by_cases heq : label n = previous
      · simp [scanRunTransitions, columnRunHeads, heq, ih]
      · have hne : previous ≠ label n := Ne.symm heq
        simp [scanRunTransitions, columnRunHeads, heq, hne, ih]

/-- Forgetting positions recovers precisely the run list used by the decoder. -/
theorem indexedBlockRuns_labels (label : ℕ → α) (start len : ℕ) :
    (indexedBlockRuns label start len).map Prod.snd =
      columnRunHeads ((blockLabelList label start len).map some) none := by
  cases len with
  | zero => rfl
  | succ len =>
      simp only [indexedBlockRuns, List.map_cons, scanRunTransitions_labels,
        blockLabelList_succ, List.map_cons, columnRunHeads]
      simp

/-- Thus cutting indexed runs into regular segments yields exactly the
same label pieces as cutting the decoder's compressed block. -/
theorem indexedBlockRuns_partition (label : ℕ → α) (start len : ℕ) (omitted : α → Bool) :
    (partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label start len)).map
        (Sum.map (List.map Prod.snd) Prod.snd) =
      partitionColumnRuns omitted (columnRunHeads ((blockLabelList label start len).map some) none) := by
  rw [← partitionColumnRuns_map, indexedBlockRuns_labels]

end TwoPointCorrelations

end OAI
