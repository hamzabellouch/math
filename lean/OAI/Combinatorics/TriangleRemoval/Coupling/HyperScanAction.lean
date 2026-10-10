import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.ClockOrder
import OAI.Combinatorics.TriangleRemoval.Process.LevelDeletes

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section GenericClockScan
variable {ι τ : Type*} [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def hyperScanAction (H : τ → Finset ι) (G : Finset ι) (T : τ) : Finset ι :=
  if H T ⊆ G then G \ H T else G

def hyperScan (H : τ → Finset ι) (G : Finset ι) (as : List τ) : Finset ι :=
  as.foldl (hyperScanAction H) G

omit [Fintype τ] [DecidableEq τ] in
theorem hyperScan_append (H : τ → Finset ι) (G : Finset ι) (as bs : List τ) :
    hyperScan H G (as ++ bs) = hyperScan H (hyperScan H G as) bs :=
  List.foldl_append

omit [Fintype τ] [DecidableEq τ] in
@[simp] theorem hyperScan_singleton (H : τ → Finset ι) (G : Finset ι) (T : τ) :
    hyperScan H G [T] = hyperScanAction H G T := rfl

omit [Fintype τ] [DecidableEq τ] in
theorem hyperScanAction_subset (H : τ → Finset ι) (G : Finset ι) (T : τ) :
    hyperScanAction H G T ⊆ G := by
  unfold hyperScanAction
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.refl G

omit [DecidableEq ι] [Fintype τ] [DecidableEq τ] in
theorem sorted_filter_lt_succ (ω : τ → ℕ) (as : List τ)
    (hs : as.Pairwise (fun a b => ω a ≤ ω b)) (k : ℕ) :
    as.filter (fun a => ω a < k + 1) =
      as.filter (fun a => ω a < k) ++ as.filter (fun a => ω a = k) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨hle, hs⟩ := List.pairwise_cons.mp hs
    by_cases hlt : ω a < k
    · have hne : ω a ≠ k := by omega
      have hlt' : ω a < k + 1 := by omega
      simp only [List.filter_cons, decide_eq_true hlt, decide_eq_true hlt',
        decide_eq_false hne, Bool.false_eq_true, ↓reduceIte, List.cons_append, ih hs]
    · by_cases heq : ω a = k
      · have hn : as.filter (fun b => ω b < k) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          have h := hle b hb
          simpa only [Bool.decide_iff] using (show ¬ω b < k by omega)
        simp only [List.filter_cons, decide_eq_false hlt, decide_eq_true heq,
          show decide (ω a < k + 1) = true by simp [heq], Bool.false_eq_true, ↓reduceIte,
          ih hs, hn, List.nil_append]
      · have hn : ¬ω a < k + 1 := by omega
        simp only [List.filter_cons, decide_eq_false hlt, decide_eq_false heq,
          decide_eq_false hn, Bool.false_eq_true, ↓reduceIte, ih hs]

omit [DecidableEq ι] in
theorem clockOrder_level_singleton (ω : τ → ℕ) (hω : Function.Injective ω) (T : τ) :
    (clockOrder ω).filter (fun a => ω a = ω T) = [T] := by
  have hd := (clockOrder_enumerates ω).1.filter (fun a => decide (ω a = ω T))
  apply List.perm_singleton.mp
  apply List.perm_of_nodup_nodup_toFinset_eq hd (by simp)
  ext a
  simp only [List.mem_toFinset, List.mem_filter, Bool.decide_iff,
    List.mem_singleton, hω.eq_iff]
  constructor
  · exact And.right
  · intro ha
    exact ⟨(enumerates_mem (clockOrder_enumerates ω) a).mpr (Finset.mem_univ _), ha⟩

omit [DecidableEq τ] in
theorem levelDeletes_one (H : τ → Finset ι) (ω : τ → ℕ)
    (hω : Function.Injective ω) (G : Finset ι) (T : τ) :
    levelDeletes H ω G (ω T) = if H T ⊆ G then H T else ∅ := by
  ext e
  simp only [mem_levelDeletes, hω.eq_iff, exists_eq_left]
  by_cases hs : H T ⊆ G <;> simp [hs]

theorem timeScan_eq_hyperScan_prefix (H : τ → Finset ι) (ω : τ → ℕ)
    (hω : Function.Injective ω) (E : Finset ι) (k : ℕ) :
    timeScan H ω E k =
      hyperScan H E ((clockOrder ω).filter (fun T => ω T < k)) := by
  induction k with
  | zero => simp [timeScan, hyperScan]
  | succ k ih =>
    rw [timeScan, ih, sorted_filter_lt_succ ω _ (clockOrder_pairwise ω) k]
    by_cases he : ∃ T, ω T = k
    · obtain ⟨T, rfl⟩ := he
      rw [clockOrder_level_singleton ω hω T, levelDeletes_one H ω hω]
      rw [hyperScan_append, hyperScan_singleton]
      unfold hyperScanAction
      split_ifs <;> simp
    · have hn : (clockOrder ω).filter (fun T => ω T = k) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro T _
        simpa only [Bool.decide_iff] using (show ¬ω T = k from fun h => he ⟨T,h⟩)
      have hd : ∀ G : Finset ι, levelDeletes H ω G k = ∅ := by
        intro G
        ext e
        simp only [mem_levelDeletes, Finset.notMem_empty, iff_false, not_exists,
          not_and]
        intro T hT
        exact False.elim (he ⟨T, hT⟩)
      rw [hn, List.append_nil, hd, Finset.sdiff_empty]

theorem timeScan_eq_hyperScan (H : τ → Finset ι) (ω : τ → ℕ)
    (hω : Function.Injective ω) (E : Finset ι) (N : ℕ) (hN : ∀ T, ω T < N) :
    timeScan H ω E N = hyperScan H E (clockOrder ω) := by
  rw [timeScan_eq_hyperScan_prefix H ω hω E N]
  congr 1
  apply List.filter_eq_self.mpr
  intro T _
  exact decide_eq_true (hN T)

end GenericClockScan
end SharpTerminalLeave

end

end OAI
