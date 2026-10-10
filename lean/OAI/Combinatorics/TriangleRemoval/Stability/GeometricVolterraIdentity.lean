import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem geometric_volterra_identity (a c : ℝ) (k : ℕ) :
    c + a * (∑ j ∈ Finset.range k, c * (1 + a) ^ j) = c * (1 + a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih]

theorem discrete_volterra_bound (E : ℕ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (M : ℕ) (hE : ∀ k ≤ M, E k ≤ c + a * ∑ j ∈ Finset.range k, E j)
    (k : ℕ) (hk : k ≤ M) : E k ≤ c * (1 + a) ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    calc
      E k ≤ c + a * ∑ j ∈ Finset.range k, E j := hE k hk
      _ ≤ c + a * ∑ j ∈ Finset.range k, c * (1 + a) ^ j := by
        gcongr with j hj
        exact ih j (Finset.mem_range.mp hj) ((Nat.le_of_lt (Finset.mem_range.mp hj)).trans hk)
      _ = c * (1 + a) ^ k := geometric_volterra_identity a c k

theorem discrete_volterra_exp_bound (E : ℕ → ℝ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (N : ℕ) (hN : 0 < N)
    (hE : ∀ k ≤ N, E k ≤ C / N + (A / N) * ∑ j ∈ Finset.range k, E j)
    (k : ℕ) (hk : k ≤ N) : E k ≤ (C / N) * Real.exp A := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 ≤ A / N := div_nonneg hA hNr.le
  have hh := discrete_volterra_bound E (A / N) (C / N) hd N hE k hk
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hC hNr.le)
  calc
    (1 + A / N) ^ k ≤ (Real.exp (A / N)) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (A / N)
    _ = Real.exp ((k : ℝ) * (A / N)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp A := by
      apply Real.exp_le_exp.mpr
      have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
      calc
        (k : ℝ) * (A / N) ≤ (N : ℝ) * (A / N) := mul_le_mul_of_nonneg_right hkr hd
        _ = A := by field_simp

theorem integral_cell_error (f : ℝ → ℝ) {a b L : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc a b, |f x - f a| ≤ L * (x - a)) :
    |(∫ x in a..b, f x) - (b - a) * f a| ≤ L * (b - a) ^ 2 := by
  have heq : (∫ x in a..b, f x) - (b - a) * f a = ∫ x in a..b, f x - f a := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f x - f a) (C := L * (b - a)) (by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact (hLip x ⟨hx.1.le, hx.2⟩).trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hL))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hb
  convert hb using 1
  ring

theorem uniform_grid_quadrature (f : ℝ → ℝ) (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|)
    (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    |(∫ x in (0 : ℝ)..((k : ℝ) / N), f x) -
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f ((j : ℝ) / N)| ≤ L / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (∫ x in (0 : ℝ)..((k : ℝ) / N), f x) =
      ∑ j ∈ Finset.range k, ∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), f x := by
    simpa only [Nat.cast_zero, zero_div] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j => (j : ℝ) / N) (n := k) (fun _ _ => hf.intervalIntegrable _ _)).symm
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        |(∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), f x) -
          (1 / N) * f ((j : ℝ) / N)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, L * (1 / (N : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast (show j + 1 ≤ N by omega)
      have hja : (j : ℝ) / N ≤ ((j + 1 : ℕ) : ℝ) / N := by
        gcongr; exact_mod_cast (Nat.le_succ j)
      have hdif : (((j + 1 : ℕ) : ℝ) / N) - (j : ℝ) / N = 1 / (N : ℝ) := by
        push_cast; ring
      have he := integral_cell_error f hja hf hL (by
        intro x hx
        have ha0 : (0 : ℝ) ≤ (j : ℝ) / N := by positivity
        have hb1 : (((j + 1 : ℕ) : ℝ) / N) ≤ 1 := by
          rw [div_le_one hNr]; simpa using hjN
        have hh := hLip x ⟨ha0.trans hx.1, hx.2.trans hb1⟩
          ((j : ℝ) / N) ⟨ha0, hja.trans hb1⟩
        simpa only [abs_of_nonneg (sub_nonneg.mpr hx.1)] using hh)
      simpa only [hdif] using he
    _ ≤ L / N := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
      calc
        _ ≤ (N : ℝ) * (L * (1 / (N : ℝ)) ^ 2) := by gcongr
        _ = L / N := by field_simp

end SharpTerminalLeave

end

end OAI
