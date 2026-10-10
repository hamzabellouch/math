import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Decompose a positive integer initial interval into dyadic shells. -/
theorem sum_dyadic_shells {E : Type*} [AddCommMonoid E] (f : ℕ → E) (J : ℕ) :
    (∑ n ∈ Finset.Ico 1 (2 ^ J), f n) =
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (m := 1) (n := 2 ^ J) (k := 2 ^ (J + 1))
      (Nat.succ_le_iff.mpr (by positivity : 0 < (2 : ℕ) ^ J))
      (Nat.pow_le_pow_right (by decide) (by omega))).symm

/-- The total cost of dyadic shells is geometric rather than logarithmic. -/
theorem norm_sum_dyadic_shells_le {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (J : ℕ) (C : ℝ)
    (hlocal : ∀ j < J,
      ‖∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n‖ ≤ C * (2 : ℝ) ^ j) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ J), f n‖ ≤ C * ((2 : ℝ) ^ J - 1) := by
  rw [sum_dyadic_shells]
  calc
    ‖∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n‖
        ≤ ∑ j ∈ Finset.range J, ‖∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, C * (2 : ℝ) ^ j :=
      Finset.sum_le_sum (fun j hj => hlocal j (Finset.mem_range.mp hj))
    _ = C * ((2 : ℝ) ^ J - 1) := by
      rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      norm_num

/-- Local bounds on the dyadic pieces of any positive integer interval sum
with constant at most two; useful for off-diagonal reciprocal phase estimates. -/
theorem norm_sum_interval_le_of_dyadic {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (Y X : ℕ) (hY : 1 ≤ Y) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ j : ℕ,
      ‖∑ n ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ Finset.Icc Y X), f n‖
        ≤ C * (2 : ℝ) ^ j) :
    ‖∑ n ∈ Finset.Icc Y X, f n‖ ≤ 2 * C * X := by
  classical
  by_cases hX : X = 0
  · subst X
    have hempty : Finset.Icc Y 0 = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp [hempty]
  let J := Nat.log 2 X + 1
  let g : ℕ → E := fun n => if n ∈ Finset.Icc Y X then f n else 0
  have htop : X < 2 ^ J := Nat.lt_pow_succ_log_self (by decide) X
  have hsub : Finset.Icc Y X ⊆ Finset.Ico 1 (2 ^ J) := by
    intro n hn
    obtain ⟨hYn, hnX⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hsum : (∑ n ∈ Finset.Icc Y X, f n) = ∑ n ∈ Finset.Ico 1 (2 ^ J), g n := by
    calc
      (∑ n ∈ Finset.Icc Y X, f n) = ∑ n ∈ Finset.Icc Y X, g n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [g, ite_eq_left hn]
      _ = ∑ n ∈ Finset.Ico 1 (2 ^ J), g n :=
        Finset.sum_subset hsub (fun n _ hn => by simp only [g, ite_eq_right hn])
  rw [hsum]
  have hblock (j : ℕ) :
      (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g n) =
        ∑ n ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ Finset.Icc Y X), f n := by
    simp only [g, ← Finset.sum_filter]
    congr 1
  have hbound := norm_sum_dyadic_shells_le g J C (fun j _ => by
    rw [hblock]
    exact hlocal j)
  have hpow : (2 : ℝ) ^ J ≤ 2 * (X : ℝ) := by
    have hh := Nat.pow_log_le_self 2 hX
    have hn : 2 ^ J ≤ 2 * X := by
      dsimp [J]
      rw [pow_succ]
      omega
    exact_mod_cast hn
  apply hbound.trans
  nlinarith

/-- Only dyadic intervals intersecting the target interval need local estimates.
Their base points lie between half the lower endpoint and the upper endpoint. -/
theorem norm_sum_interval_le_of_local_intervals {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (Y X : ℕ) (hY : 1 ≤ Y) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ U : ℕ, 0 < U → Y ≤ 2 * U → U ≤ X →
      ‖∑ n ∈ (Finset.Ico U (2 * U) ∩ Finset.Icc Y X), f n‖ ≤ C * U) :
    ‖∑ n ∈ Finset.Icc Y X, f n‖ ≤ 2 * C * X := by
  apply norm_sum_interval_le_of_dyadic f Y X hY C hC
  intro j
  by_cases hempty : Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ Finset.Icc Y X = ∅
  · rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    positivity
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hd, hi⟩ := Finset.mem_inter.mp hn
    obtain ⟨hUn, hnU⟩ := Finset.mem_Ico.mp hd
    obtain ⟨hYn, hnX⟩ := Finset.mem_Icc.mp hi
    have hYbound : Y ≤ 2 * 2 ^ j := by
      rw [pow_succ] at hnU
      omega
    have hupper : 2 ^ j ≤ X := hUn.trans hnX
    have hh := hlocal (2 ^ j) (by positivity) hYbound hupper
    simpa [pow_succ, Nat.mul_comm] using hh

end Problem337

end

end OAI
