import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace PoissonProfile

theorem eq_pow_div_factorial_mul_zero (k : ℝ) (p : ℕ → ℝ)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = k * p n) :
    ∀ n : ℕ, p n = k ^ n / (n.factorial : ℝ) * p 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have h := hrec n
    rw [ih] at h
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    apply (mul_left_cancel₀ hn)
    calc
      (n + 1 : ℝ) * p (n + 1) = k * (k ^ n / (n.factorial : ℝ) * p 0) := h
      _ = (n + 1 : ℝ) * (k ^ n * k / ((n + 1) * (n.factorial : ℝ)) * p 0) := by
        field_simp

theorem factorization (k : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j) :
    ∀ i j : ℕ, P i j = k ^ i / (i.factorial : ℝ) * P 0 j := by
  intro i j
  exact eq_pow_div_factorial_mul_zero k (fun i => P i j) (fun i => hrec i j) i

theorem column_hasSum (k : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (j : ℕ) : HasSum (fun i => P i j) (Real.exp k * P 0 j) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp k).mul_right (P 0 j)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.congr_fun (fun i => factorization k P hrec i j)

theorem factorization_marginal (k : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (i j : ℕ) :
    P i j = (Real.exp (-k) * k ^ i / (i.factorial : ℝ)) * (∑' a, P a j) := by
  rw [(column_hasSum k P hrec j).tsum_eq, factorization k P hrec i j]
  have he : Real.exp (-k) * Real.exp k = 1 := by rw [← Real.exp_add]; simp
  calc
    k ^ i / (i.factorial : ℝ) * P 0 j =
        (Real.exp (-k) * Real.exp k) * (k ^ i / (i.factorial : ℝ) * P 0 j) := by rw [he, one_mul]
    _ = Real.exp (-k) * k ^ i / (i.factorial : ℝ) * (Real.exp k * P 0 j) := by ring

theorem weighted_total_eq_exp_mul_row (k : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (w : ℕ → ℝ) :
    (∑' i, ∑' j, w j * P i j) = Real.exp k * (∑' j, w j * P 0 j) := by
  calc
    (∑' i, ∑' j, w j * P i j) =
        ∑' i : ℕ, (k ^ i / (i.factorial : ℝ)) * (∑' j, w j * P 0 j) := by
      apply tsum_congr
      intro i
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      rw [factorization k P hrec i j]
      ring
    _ = (∑' i : ℕ, k ^ i / (i.factorial : ℝ)) * (∑' j, w j * P 0 j) :=
      tsum_mul_right
    _ = Real.exp k * (∑' j, w j * P 0 j) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp k).tsum_eq, ← Real.exp_eq_exp_ℝ]

theorem weighted_row_eq_exp_neg_mul_total (k : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (w : ℕ → ℝ) :
    (∑' j, w j * P 0 j) = Real.exp (-k) * (∑' i, ∑' j, w j * P i j) := by
  rw [weighted_total_eq_exp_mul_row k P hrec w, ← mul_assoc, ← Real.exp_add]
  simp

theorem first_moment_row (k c : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (hmean : (∑' i, ∑' j : ℕ, (j : ℝ) * P i j) = c) :
    (∑' j : ℕ, (j : ℝ) * P 0 j) = Real.exp (-k) * c := by
  rw [weighted_row_eq_exp_neg_mul_total k P hrec (fun j : ℕ => (j : ℝ)), hmean]

theorem row_rigidity (p : ℕ → ℝ) (μ c : ℝ)
    (hpos : 0 < μ) (hc : c ≤ 1) (hp : ∀ n, 0 ≤ p n) (hp0 : p 0 = 0)
    (hsum : HasSum p μ) (hmoment : HasSum (fun n : ℕ => (n : ℝ) * p n) (c * μ)) :
    c = 1 ∧ p 1 = μ ∧ ∀ n : ℕ, n ≠ 1 → p n = 0 := by
  have hdom : ∀ n : ℕ, p n ≤ (n : ℝ) * p n := by
    intro n
    cases n with
    | zero => simp [hp0]
    | succ n =>
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [hp (n + 1), Nat.cast_nonneg (α := ℝ) n]
  have hle : μ ≤ c * μ := hasSum_le hdom hsum hmoment
  have hc1 : c = 1 := by nlinarith
  have hdif : HasSum (fun n : ℕ => (n : ℝ) * p n - p n) 0 := by
    simpa [hc1] using hmoment.sub hsum
  have hzero : ∀ n : ℕ, n ≠ 1 → p n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · simpa [hn0] using hp0
    have hn2 : 2 ≤ n := by omega
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hterm := le_hasSum hdif n (fun j _ => sub_nonneg.mpr (hdom j))
    nlinarith [hp n]
  refine ⟨hc1, ?_, hzero⟩
  calc
    p 1 = ∑' n, p n := (tsum_eq_single 1 hzero).symm
    _ = μ := hsum.tsum_eq

theorem column_zero_of_first_zero (k : ℝ) (P : ℕ → ℕ → ℝ)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    {j : ℕ} (hz : P 0 j = 0) : ∀ i : ℕ, P i j = 0 := by
  intro i
  rw [factorization k P hrec i j, hz, mul_zero]

theorem supported_on_one (k : ℝ) (P : ℕ → ℕ → ℝ) (μ c : ℝ)
    (hpos : 0 < μ) (hc : c ≤ 1) (hp : ∀ j, 0 ≤ P 0 j) (hp00 : P 0 0 = 0)
    (hsum : HasSum (P 0) μ)
    (hmoment : HasSum (fun j : ℕ => (j : ℝ) * P 0 j) (c * μ))
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j) :
    ∀ i j : ℕ, j ≠ 1 → P i j = 0 := by
  have hz := (row_rigidity (P 0) μ c hpos hc hp hp00 hsum hmoment).2.2
  intro i j hj
  exact column_zero_of_first_zero k P hrec (hz j hj) i

theorem no_uncovered_mass (k : ℝ) (P : ℕ → ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hp00 : P 0 0 = 0)
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (huncovered : δ ≤ ∑' i, P i 0) : False := by
  have hz := column_zero_of_first_zero k P hrec hp00
  have hsumzero : (∑' i, P i 0) = 0 := by simp [hz]
  linarith

end PoissonProfile
end Balanced

end OAI
