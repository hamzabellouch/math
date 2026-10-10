import OAI.NumberTheory.TwoPointCorrelations.MRTMeanSquare
import Mathlib.NumberTheory.LSeries.Basic

namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset
open scoped BigOperators

theorem mrt_dirichlet_mean_square_subset (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ = ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) := by
        apply sum_congr rfl
        intro n _
        have he (a b : ℝ) : (-a - -b) ^ 2 = (a - b) ^ 2 := by ring
        simp only [he]
      _ ≤ _ := mrt_logarithmic_kernel_row hT (hS hm)
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring

noncomputable def mrtDyadicPolynomial (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial (Ioc N (2 * N))
    (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t

lemma mrt_line_one_term (b : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term b (1 + (t : ℂ) * Complex.I) n =
      b n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  congr 1
  push_cast
  ring_nf

lemma mrtDyadicPolynomial_eq_LSeries (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial b N t =
      ∑ n ∈ Ioc N (2 * N), LSeries.term b (1 + (t : ℂ) * Complex.I) n := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro n hn
  exact (mrt_line_one_term b (by have := (mem_Ioc.mp hn).1; omega) t).symm

/-- On the line `Re(s)=1`, a one-bounded dyadic polynomial has mean square
`O(T/N+1)`, with the absolute constant `16e`. -/
theorem mrt_dyadic_mean_square (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ 1) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤
      16 * Real.exp 1 * (T / (N : ℝ) + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (∑ n ∈ Ioc N (2 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤ (N : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ n ∈ Ioc N (2 * N), ((n : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hN.trans (mem_Ioc.mp hn).1
        rw [norm_div, Complex.norm_natCast]
        calc
          _ ≤ (1 / (n : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (hb n hn) hn0.le) 2
          _ = _ := by simp
      _ ≤ (N : ℝ)⁻¹ - ((2 * N : ℕ) : ℝ)⁻¹ :=
        sum_Ioc_inv_sq_le_sub (α := ℝ) hN.ne' (by omega)
      _ ≤ _ := sub_le_self _ (by positivity)
  have hbound := mrt_dirichlet_mean_square_subset (Ioc N (2 * N))
    (N := 2 * N) (by
      intro n hn
      have hn' := mem_Ioc.mp hn
      exact mem_Ioc.mpr ⟨by omega, hn'.2⟩)
    (fun n => b n / (n : ℂ)) hT
  change (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤ _ at hbound
  apply hbound.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + ((2 * N : ℕ) : ℝ)) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 8 * Real.exp 1 * (T / (N : ℝ) + 2) := by
      push_cast
      field_simp
    _ ≤ _ := by nlinarith [div_nonneg hT.le hNr.le, Real.exp_pos 1]

end TwoPointCorrelations

end OAI
