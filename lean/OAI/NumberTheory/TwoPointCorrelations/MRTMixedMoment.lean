import OAI.NumberTheory.TwoPointCorrelations.MRTMixedCoefficients
import OAI.NumberTheory.TwoPointCorrelations.MRTWeightedTail

namespace OAI

/-! Mean square of the actual mixed prime/cofactor coefficients. The
factorial cost is explicit, while the finite Euler factor depends only on
the preceding short prime band, not the number of typical-set masks. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_factored_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {L U : ℕ}
    (hL : 0 < L) (hLU : L ≤ U) {A : ℝ}
    (hb : ∀ n ∈ Ioc L U, ‖b n‖ ≤ A *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card : ℝ)) :
    (∑ n ∈ Ioc L U, ‖b n / (n : ℂ)‖ ^ 2) ≤
      (2 / (L : ℝ)) * A ^ 2 * (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  let S := mrtFactoredUpTo P U
  let g : ℕ → ℝ := fun n => ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2
  let E := ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹
  have hE : 0 ≤ E := by
    apply prod_nonneg
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    exact inv_nonneg.mpr (by linarith)
  have hpref (n : ℕ) (_hn : n ≤ U) : (∑ i ∈ Icc 1 n, g i) ≤ E ^ 3 * n := by
    have hc := mrt_divisor_count_second_moment S
      (fun _ hd => mrtFactoredUpTo_pos P U hd)
      (fun _ hd _ he hed => mrtFactoredUpTo_divisor_closed P U hd he hed) n
    calc
      _ ≤ (n : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := hc
      _ ≤ (n : ℝ) * E ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity))
          (mrt_factored_reciprocal_sum P hP U) 3
      _ = _ := mul_comm _ _
  have ht := mrt_weighted_square_tail g (fun _ => sq_nonneg _) hL hLU
    (pow_nonneg hE 3) hpref
  calc
    _ ≤ ∑ n ∈ Ioc L U, A ^ 2 * (g n / (n : ℝ) ^ 2) := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast, div_pow]
      apply (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2) (sq_nonneg _)).trans_eq
      dsimp [g]
      ring
    _ = A ^ 2 * ∑ n ∈ Ioc L U, g n / (n : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ A ^ 2 * (2 * E ^ 3 / L) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg A)
    _ = _ := by ring

theorem mrt_mixed_coefficient_mean_square (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc L U)
      (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
      (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  have hs : Ioc L U ⊆ Ioc 0 U := by
    intro n hn
    exact mem_Ioc.mpr ⟨lt_of_lt_of_le hL (mem_Ioc.mp hn).1.le, (mem_Ioc.mp hn).2⟩
  apply (mrt_dirichlet_mean_square_subset (Ioc L U) (N := U) hs
    (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ)) hT).trans
  have hmass := mrt_factored_coefficient_mass P hP
    (mrtMixedPrimeCoefficient P M a b r) hL hLU
    (fun n hn => mrt_mixed_prime_coefficient_bound P M hP a b ha hb r
      (lt_of_lt_of_le hL (mem_Ioc.mp hn).1.le) (mem_Ioc.mp hn).2)
  calc
    _ ≤ (8 * Real.exp 1 * (T + U)) *
        ((2 / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
          (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
