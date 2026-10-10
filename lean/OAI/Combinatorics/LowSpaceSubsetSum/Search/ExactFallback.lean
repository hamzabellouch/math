import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDictionary

namespace OAI

/-! # The exact small-input fallback as a depth-first subset search

The loop keeps the current target and a suffix of the input. It does not
materialize the powerset. The work bound holds even when no branch accepts.
-/

namespace LowSpaceSubsetSum.ExactFallback

variable {ι : Type*}

def run (a : ι → ℤ) : List ι → ℤ → Bool × ℕ
  | [], target => (decide (target = 0), 1)
  | x :: xs, target =>
    let left := run a xs target
    if left.1 then (true, left.2 + 1)
    else
      let right := run a xs (target - a x)
      (right.1, left.2 + right.2 + 1)

theorem run_work (a : ι → ℤ) (xs : List ι) (target : ℤ) :
    (run a xs target).2 ≤ 2 ^ (xs.length + 1) - 1 := by
  induction xs generalizing target with
  | nil => simp [run]
  | cons x xs ih =>
    have hl := ih target
    have hr := ih (target - a x)
    have hp : 1 ≤ 2 ^ (xs.length + 1) := Nat.one_le_two_pow
    simp only [run]
    split <;> dsimp only
    · rw [List.length_cons, Nat.add_assoc, pow_succ]
      omega
    · rw [List.length_cons, Nat.add_assoc, pow_succ]
      omega

theorem run_accepts (a : ι → ℤ) (xs : List ι) (target : ℤ) :
    (run a xs target).1 = true ↔
      ∃ ys ∈ xs.sublists, (ys.map a).sum = target := by
  induction xs generalizing target with
  | nil => simp [run, eq_comm]
  | cons x xs ih =>
    have he : (run a (x :: xs) target).1 = true ↔
        (run a xs target).1 = true ∨ (run a xs (target - a x)).1 = true := by
      simp only [run]
      split <;> simp_all
    rw [he, ih, ih, List.sublists_cons]
    simp only [List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (⟨ys, hy, he⟩ | ⟨ys, hy, he⟩)
      · exact ⟨ys, ⟨ys, hy, Or.inl rfl⟩, he⟩
      · refine ⟨x :: ys, ⟨ys, hy, Or.inr rfl⟩, ?_⟩
        simp only [List.map_cons, List.sum_cons]
        omega
    · rintro ⟨ys, ⟨zs, hz, rfl | rfl⟩, he⟩
      · exact Or.inl ⟨ys, hz, he⟩
      · refine Or.inr ⟨zs, hz, ?_⟩
        simp only [List.map_cons, List.sum_cons] at he
        omega

variable [Fintype ι] [DecidableEq ι]

theorem weight_eq_list_sum (a : ι → ℤ) (ys : List ι) (hy : ys.Nodup) :
    weight a ys.toFinset = (ys.map a).sum := by
  have hw : weight a ys.toFinset = ∑ i ∈ ys.toFinset, a i := by
    unfold weight
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  rw [hw, List.sum_toFinset a hy]

theorem run_correct (a : ι → ℤ) (xs : List ι) (hx : xs.Nodup) (target : ℤ) :
    (run a xs target).1 = true ↔ ∃ S ⊆ xs.toFinset, weight a S = target := by
  rw [run_accepts]
  constructor
  · rintro ⟨ys, hy, he⟩
    have hsub := List.mem_sublists.mp hy
    refine ⟨ys.toFinset, ?_, ?_⟩
    · intro i hi
      exact List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hi))
    rw [weight_eq_list_sum a ys (hx.sublist hsub)]
    exact he
  · rintro ⟨S, hS, he⟩
    let ys := xs.filter (fun i => i ∈ S)
    have hys : ys.toFinset = S := by
      ext i
      simp only [ys, List.toFinset_filter, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hi => ⟨hS hi, hi⟩⟩
    refine ⟨ys, List.mem_sublists.mpr List.filter_sublist, ?_⟩
    rw [← weight_eq_list_sum a ys (hx.sublist List.filter_sublist), hys]
    exact he

def decision {n : ℕ} (I : Instance n) : Bool :=
  (run (fun i => (I.values i : ℤ)) (List.finRange n) I.target).1

theorem decision_correct {n : ℕ} (I : Instance n) : decision I = true ↔ Solvable I := by
  rw [decision, run_correct _ _ (List.nodup_finRange n)]
  simp only [List.toFinset_finRange, Finset.subset_univ, true_and, Solvable]

end ExactFallback
end LowSpaceSubsetSum

end OAI
