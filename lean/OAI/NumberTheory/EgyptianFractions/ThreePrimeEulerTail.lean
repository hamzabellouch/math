import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeEulerTail

/-- A reciprocal-square tail is bounded by a telescoping reciprocal tail.
The statement is for arbitrary finite sets, hence also for sets of primes. -/
theorem reciprocal_square_tail (P : Finset ℕ) (N : ℕ) (hN : 2 ≤ N)
    (hP : ∀ p ∈ P, N < p) :
    (∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 / ((N : ℝ) - 1) := by
  classical
  by_cases hempty : P = ∅
  · subst P
    simp only [Finset.sum_empty]
    apply one_div_nonneg.mpr
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let M := P.max' hne
  have hNM : N < M := hP M (Finset.max'_mem P hne)
  have hsub : P ⊆ Finset.Ico (N + 1) (M + 1) := by
    intro p hp
    exact Finset.mem_Ico.mpr ⟨by have := hP p hp; omega,
      by have := Finset.le_max' P p hp; omega⟩
  have hpoint (p : ℕ) (hp : p ∈ Finset.Ico (N + 1) (M + 1)) :
      1 / ((p : ℝ) - 1) ^ 2 ≤
        1 / ((p : ℝ) - 2) - 1 / (((p + 1 : ℕ) : ℝ) - 2) := by
    have hp3 : 3 ≤ p := by have := (Finset.mem_Ico.mp hp).1; omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    have hp2 : 0 < (p : ℝ) - 2 := by linarith
    push_cast
    have heq : (p : ℝ) + 1 - 2 = (p : ℝ) - 1 := by ring
    rw [heq]
    field_simp
    nlinarith
  calc
    _ ≤ ∑ p ∈ Finset.Ico (N + 1) (M + 1), 1 / ((p : ℝ) - 1) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ ∑ p ∈ Finset.Ico (N + 1) (M + 1),
        (1 / ((p : ℝ) - 2) - 1 / (((p + 1 : ℕ) : ℝ) - 2)) :=
      Finset.sum_le_sum hpoint
    _ = 1 / (((N + 1 : ℕ) : ℝ) - 2) -
        1 / (((M + 1 : ℕ) : ℝ) - 2) := by
      have htel := Finset.sum_Ico_sub (fun p : ℕ => -(1 / ((p : ℝ) - 2)))
        (show N + 1 ≤ M + 1 by omega)
      simpa only [neg_sub_neg] using htel
    _ ≤ 1 / ((N : ℝ) - 1) := by
      have hM : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
      have hpos : 0 ≤ 1 / (((M + 1 : ℕ) : ℝ) - 2) := by
        apply one_div_nonneg.mpr
        push_cast
        linarith
      push_cast at *
      have heq : (N : ℝ) + 1 - 2 = (N : ℝ) - 1 := by ring
      rw [heq]
      linarith

/-- Uniform finite Euler-tail error from the standard local-factor defect bound. -/
theorem product_tail_abs_sub_one (f : ℕ → ℝ) (P : Finset ℕ)
    (N : ℕ) (hN : 2 ≤ N) (hP : ∀ p ∈ P, N < p)
    (hf : ∀ p ∈ P, |f p - 1| ≤ 1 / ((p : ℝ) - 1) ^ 2) :
    |(∏ p ∈ P, f p) - 1| ≤ 2 / ((N : ℝ) - 1) := by
  have hsum : (∑ p ∈ P, |f p - 1|) ≤ 1 / ((N : ℝ) - 1) :=
    (Finset.sum_le_sum hf).trans (reciprocal_square_tail P N hN hP)
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) - 1 := by linarith
  have hsmall : |1 / ((N : ℝ) - 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one hden).mpr (by linarith)
  have hprod := P.norm_prod_one_add_sub_one_le (fun p => f p - 1)
  simp only [add_sub_cancel, Real.norm_eq_abs] at hprod
  calc
    _ ≤ Real.exp (∑ p ∈ P, |f p - 1|) - 1 := hprod
    _ ≤ Real.exp (1 / ((N : ℝ) - 1)) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1
    _ ≤ |Real.exp (1 / ((N : ℝ) - 1)) - 1| := le_abs_self _
    _ ≤ 2 * |1 / ((N : ℝ) - 1)| := Real.abs_exp_sub_one_le hsmall
    _ = 2 / ((N : ℝ) - 1) := by rw [abs_of_nonneg (by positivity)]; ring

/-- The local-factor defect majorant gives absolute summability without imposing
any condition on the finitely many initial factors. -/
theorem summable_abs_sub_one (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, 3 ≤ p → |f p - 1| ≤ 1 / ((p : ℝ) - 1) ^ 2) :
    Summable (fun p => |f p - 1|) := by
  have hseries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 2).mpr hseries
  apply (summable_nat_add_iff 3).mp
  apply hshift.of_nonneg_of_le (fun n => abs_nonneg _)
  intro n
  have h := hf (n + 3) (by omega)
  convert h using 1
  push_cast
  ring

/-- Absolute summability of the local defects defines a genuine Euler product. -/
theorem multipliable (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, 3 ≤ p → |f p - 1| ≤ 1 / ((p : ℝ) - 1) ^ 2) :
    Multipliable f := by
  have hsum : Summable (fun p => f p - 1) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using summable_abs_sub_one f hf
  simpa only [add_sub_cancel] using Real.multipliable_one_add_of_summable hsum

/-- A partial Euler product approximates its infinite product with an explicit
relative error. Only the universal local defect estimate is needed. -/
theorem tprod_sub_partial_abs_le (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, 3 ≤ p → |f p - 1| ≤ 1 / ((p : ℝ) - 1) ^ 2)
    (N : ℕ) (hN : 2 ≤ N) :
    |(∏' p, f p) - ∏ p ∈ Finset.range (N + 1), f p| ≤
      |∏ p ∈ Finset.range (N + 1), f p| * (2 / ((N : ℝ) - 1)) := by
  apply le_of_tendsto (((multipliable f hf).hasProd.tendsto_prod_nat.sub_const
    (∏ p ∈ Finset.range (N + 1), f p)).abs)
  filter_upwards [Filter.eventually_ge_atTop (N + 1)] with M hNM
  rw [← Finset.prod_range_mul_prod_Ico f hNM]
  have heq : (∏ p ∈ Finset.range (N + 1), f p) *
      (∏ p ∈ Finset.Ico (N + 1) M, f p) -
      (∏ p ∈ Finset.range (N + 1), f p) =
      (∏ p ∈ Finset.range (N + 1), f p) *
        ((∏ p ∈ Finset.Ico (N + 1) M, f p) - 1) := by ring
  rw [heq, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply product_tail_abs_sub_one f _ N hN
  · intro p hp
    have := (Finset.mem_Ico.mp hp).1
    omega
  · intro p hp
    apply hf
    have := (Finset.mem_Ico.mp hp).1
    omega

/-- All partial products are bounded by three times their first three factors.
This estimate is uniform in any external parameter of the local factors. -/
theorem partial_abs_le (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, 3 ≤ p → |f p - 1| ≤ 1 / ((p : ℝ) - 1) ^ 2)
    (N : ℕ) (hN : 2 ≤ N) :
    |∏ p ∈ Finset.range (N + 1), f p| ≤
      3 * |∏ p ∈ Finset.range 3, f p| := by
  rw [← Finset.prod_range_mul_prod_Ico f (show 3 ≤ N + 1 by omega), abs_mul]
  have htail := product_tail_abs_sub_one f (Finset.Ico 3 (N + 1)) 2 (by omega)
    (by intro p hp; have := (Finset.mem_Ico.mp hp).1; omega)
    (by intro p hp; exact hf p (Finset.mem_Ico.mp hp).1)
  norm_num only [Nat.cast_ofNat, sub_self, one_div, Nat.cast_one, sub_zero] at htail
  have hbound : |∏ p ∈ Finset.Ico 3 (N + 1), f p| ≤ 3 := by
    calc
      _ = |((∏ p ∈ Finset.Ico 3 (N + 1), f p) - 1) + 1| := by ring_nf
      _ ≤ |(∏ p ∈ Finset.Ico 3 (N + 1), f p) - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 3 := by norm_num at htail ⊢; linarith
  nlinarith [abs_nonneg (∏ p ∈ Finset.range 3, f p)]

/-- Uniform O(1/N) truncation error, stated with a bound for the only three
uncontrolled initial local factors. -/
theorem tprod_sub_partial_abs_le_uniform (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, 3 ≤ p → |f p - 1| ≤ 1 / ((p : ℝ) - 1) ^ 2)
    (B : ℝ) (hB : |∏ p ∈ Finset.range 3, f p| ≤ B)
    (N : ℕ) (hN : 2 ≤ N) :
    |(∏' p, f p) - ∏ p ∈ Finset.range (N + 1), f p| ≤
      6 * B / ((N : ℝ) - 1) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) - 1 := by linarith
  calc
    _ ≤ |∏ p ∈ Finset.range (N + 1), f p| * (2 / ((N : ℝ) - 1)) :=
      tprod_sub_partial_abs_le f hf N hN
    _ ≤ (3 * B) * (2 / ((N : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (partial_abs_le f hf N hN).trans (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = 6 * B / ((N : ℝ) - 1) := by ring

end Problem337.ThreePrimeEulerTail

end

end OAI
