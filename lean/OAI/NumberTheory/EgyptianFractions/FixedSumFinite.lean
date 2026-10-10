import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Ordered positive denominator tuples with a prescribed rational sum.
Repetitions are allowed. -/
def OrderedUnitSums (k : ℕ) (x : ℚ) : Set (Fin k → ℕ) :=
  {n | (∀ i, 0 < n i) ∧ Monotone n ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = x}

lemma ordered_unit_sum_pos {k : ℕ} {x : ℚ} {n : Fin (k + 1) → ℕ}
    (hn : n ∈ OrderedUnitSums (k + 1) x) : 0 < x := by
  rw [← hn.2.2]
  apply Finset.sum_pos
  · intro i _
    exact div_pos (by norm_num) (by exact_mod_cast hn.1 i)
  · exact Finset.univ_nonempty

lemma ordered_unit_first_bound {k : ℕ} {x : ℚ} {n : Fin (k + 1) → ℕ}
    (hn : n ∈ OrderedUnitSums (k + 1) x) :
    n 0 ≤ ⌈((k + 1 : ℕ) : ℚ) / x⌉₊ := by
  have hx : 0 < x := ordered_unit_sum_pos hn
  have hn0 : (0 : ℚ) < n 0 := by exact_mod_cast hn.1 0
  have hsum : x ≤ ((k + 1 : ℕ) : ℚ) / (n 0 : ℚ) := by
    rw [← hn.2.2]
    calc
      (∑ i : Fin (k + 1), (1 : ℚ) / (n i : ℚ)) ≤
          ∑ _i : Fin (k + 1), (1 : ℚ) / (n 0 : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le hn0
        exact_mod_cast hn.2.1 (Fin.zero_le i)
      _ = ((k + 1 : ℕ) : ℚ) / (n 0 : ℚ) := by simp [div_eq_mul_inv]
  have hmul : x * (n 0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := (le_div_iff₀ hn0).mp hsum
  have hfirst : (n 0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) / x := by
    apply (le_div_iff₀ hx).2
    simpa [mul_comm] using hmul
  exact_mod_cast hfirst.trans (Nat.le_ceil _)

/-- For every fixed length and fixed rational total, there are only finitely
many nondecreasing tuples of positive unit-fraction denominators. -/
theorem ordered_unit_sums_finite (k : ℕ) (x : ℚ) :
    Set.Finite (OrderedUnitSums k x) := by
  induction k generalizing x with
  | zero => exact Set.toFinite _
  | succ k ih =>
    classical
    let B : ℕ := ⌈((k + 1 : ℕ) : ℚ) / x⌉₊
    have hfinite : (⋃ d ∈ Set.Icc 1 B,
        (fun t : Fin k → ℕ => Fin.cons (n := k) (α := fun _ => ℕ) d t) '' OrderedUnitSums k (x - (1 : ℚ) / (d : ℚ))).Finite := by
      apply (Set.finite_Icc 1 B).biUnion
      intro d _
      exact (ih _).image (fun t : Fin k → ℕ => Fin.cons (n := k) (α := fun _ => ℕ) d t)
    apply hfinite.subset
    intro n hn
    apply Set.mem_iUnion.2 ⟨n 0, ?_⟩
    apply Set.mem_iUnion.2 ⟨?_, ?_⟩
    · exact ⟨hn.1 0, ordered_unit_first_bound hn⟩
    · refine ⟨Fin.tail n, ?_, Fin.cons_self_tail n⟩
      refine ⟨fun i => hn.1 i.succ, ?_, ?_⟩
      · intro i j hij
        exact hn.2.1 (Fin.succ_le_succ_iff.mpr hij)
      · have hsum := hn.2.2
        rw [Fin.sum_univ_succ] at hsum
        change (∑ i : Fin k, (1 : ℚ) / (n i.succ : ℚ)) = _
        linarith

end Problem337

end

end OAI
