import OAI.Combinatorics.LowSpaceSubsetSum.Streams.TieReplay
import Mathlib.Data.List.TakeWhile

namespace OAI

/-!
# Reporting the stored part of a tie group

The immutable buffer is traversed by one natural index. The same bounded
reporter used for a generator suffix applies, so buffer reporting shares
the all-outcome stop and query bounds without keeping an output list.
-/

namespace LowSpaceSubsetSum
namespace BufferReplay

universe u w

variable {α : Type u} {τ : Type w}

def read (xs : Array α) (i : ℕ) : Option (α × ℕ) :=
  if hi : i < xs.size then some (xs[i], i + 1) else none

def view (xs : Array α) (i : ℕ) : List α := xs.toList.drop i

theorem isReader (xs : Array α) : RowMerge.IsReader (read xs) (view xs) := by
  intro i
  by_cases hi : i < xs.size
  · dsimp only [read]
    rw [dite_eq_left hi]
    change xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1)
    simpa using List.drop_eq_getElem_cons (show i < xs.toList.length by simpa using hi)
  · dsimp only [read]
    rw [dite_eq_right hi]
    change xs.toList.drop i = []
    apply List.drop_eq_nil_of_le
    simpa using Nat.le_of_not_gt hi

def run (key : α → ℤ) (K : ℤ) (report : α → τ → τ × Bool) (xs : Array α) (a : τ) :
    TieReplay.Result ℕ τ := TieReplay.run (read xs) key K report xs.size 0 a

theorem queries_le (key : α → ℤ) (K : ℤ) (report : α → τ → τ × Bool)
    (xs : Array α) (a : τ) : (run key K report xs a).queries ≤ xs.size :=
  TieReplay.run_queries_le (read xs) key K report (view xs) (isReader xs) xs.size 0 a

theorem reports_le (key : α → ℤ) (K : ℤ) (report : α → τ → τ × Bool)
    (xs : Array α) (a : τ) : (run key K report xs a).reports ≤ xs.size := by
  have h := TieReplay.run_reports_le_potential (read xs) key K report
    (view xs) (isReader xs) xs.size 0 a
  have hlen : (TieBuffer.groupView key K (view xs) 0).length ≤ xs.size := by
    simpa [TieBuffer.groupView, view] using
      (List.takeWhile_sublist (l := xs.toList) (fun x => decide (key x = K))).length_le
  exact h.trans hlen

theorem state_complete (key : α → ℤ) (K : ℤ) (report : α → τ → τ × Bool)
    (hreport : ∀ x a, (report x a).2 = false) (xs : Array α) (a : τ)
    (hkeys : ∀ x ∈ xs.toList, key x = K) :
    (run key K report xs a).state = xs.toList.foldl (fun a x => (report x a).1) a := by
  have hgroup : TieBuffer.groupView key K (view xs) 0 = xs.toList := by
    simp only [TieBuffer.groupView, view, List.drop_zero]
    apply List.takeWhile_eq_self_iff.mpr
    simpa only [decide_eq_true_eq] using hkeys
  have h := TieReplay.run_state_complete (read xs) key K report hreport (view xs)
    (isReader xs) xs.size 0 a (by simp [hgroup])
  simpa [run, hgroup] using h

theorem filled_buffer_keys {σ : Type*} (reader : σ → Option (α × σ))
    (key : α → ℤ) (K : ℤ) (output : σ → List α)
    (hreader : RowMerge.IsReader reader output) (B : ℕ) (s : σ) :
    ∀ x ∈ (TieBuffer.fill reader key K B s).buffer.toList, key x = K := by
  rw [TieBuffer.fill_buffer reader key K output hreader B s]
  intro x hx
  have htake : x ∈ (output s).takeWhile (fun y => decide (key y = K)) :=
    List.mem_of_mem_take hx
  have htrue : decide (key x = K) = true := List.mem_takeWhile_imp (p := fun y => decide (key y = K)) htake
  exact of_decide_eq_true htrue

end BufferReplay
end LowSpaceSubsetSum

end OAI
