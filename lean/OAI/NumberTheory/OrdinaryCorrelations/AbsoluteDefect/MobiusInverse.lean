import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights

noncomputable def mobiusInverse (z : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ n.divisorsAntidiagonal, (μ a.1 : ℝ) * z a.2

theorem sum_mobiusInverse (z : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, mobiusInverse z a = z n := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    (fun _ _ => rfl)) n hn

theorem upper_divisor_sum {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P)
    (F : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then F (P / d) else 0) =
      ∑ a ∈ (P / l).divisors, F a := by
  calc
    _ = ∑ a ∈ P.divisors, if l ∣ P / a then F a else 0 := by
      rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then F (P / d) else 0)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hP]
    _ = ∑ a ∈ P.divisors, if a ∣ P / l then F a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have haP := Nat.dvd_of_mem_divisors ha
      simp only [Nat.dvd_div_iff_mul_dvd haP, Nat.dvd_div_iff_mul_dvd hl, Nat.mul_comm a l]
    _ = _ := by
      rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]

noncomputable def upperInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  mobiusInverse (fun a => y (P / a)) (P / d)

theorem upperInverse_sum {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then upperInverse P y d else 0) = y l := by
  simp only [upperInverse]
  rw [upper_divisor_sum hP hl]
  rw [sum_mobiusInverse _ (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl))), Nat.div_div_self hl hP]

theorem upperInverse_one {P : ℕ} (hP : P ≠ 0) (y : ℕ → ℝ) :
    upperInverse P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  simp only [upperInverse, Nat.div_one, mobiusInverse]
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (μ d : ℝ) * y (P/e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

noncomputable def mass (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors, if l ≤ z then s.selbergTerms l else 0

noncomputable def target (s : BoundingSieve) (z l : ℕ) : ℝ :=
  if l ≤ z then (μ l : ℝ) * s.selbergTerms l / mass s z else 0

noncomputable def weights (s : BoundingSieve) (z d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * upperInverse s.prodPrimes (target s z) d

theorem mass_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) : 0 < mass s z := by
  apply Finset.sum_pos'
  · intro l hl
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).le
    · exact le_rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, ?_⟩
    simpa only [ite_eq_left hz] using s.selbergTerms_pos (one_dvd s.prodPrimes)

theorem weights_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    weights s z 1 = 1 := by
  rw [weights, s.nu_mult.map_one, inv_one, one_mul, upperInverse_one s.prodPrimes_ne_zero]
  have heq : (∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * target s z d) =
      mass s z / mass s z := by
    change _ = (∑ l ∈ s.prodPrimes.divisors, if l ≤ z then s.selbergTerms l else 0) / _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hsq : (μ d : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
    simp only [target]
    split_ifs
    · rw [← mul_div_assoc, ← mul_assoc, ← pow_two, hsq, one_mul]
    · simp
  rw [heq, div_self (mass_pos s hz).ne']

theorem weights_upper_sum (s : BoundingSieve) (z : ℕ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * weights s z d else 0) =
      target s z l := by
  convert upperInverse_sum s.prodPrimes_ne_zero hl (target s z) using 1
  apply Finset.sum_congr rfl
  intro d hd
  simp only [weights, ← mul_assoc, mul_inv_cancel₀
    (s.nu_pos_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd)).ne', one_mul]

theorem weights_mainSum (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (weights s z)) = (mass s z)⁻¹ := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have heq : (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
      (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * weights s z d else 0) ^ 2) =
      mass s z / (mass s z)^2 := by
    change _ = (∑ l ∈ s.prodPrimes.divisors, if l ≤ z then s.selbergTerms l else 0) / _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    rw [weights_upper_sum s z (Nat.dvd_of_mem_divisors hl), target]
    have hg := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
    have hm := (mass_pos s hz).ne'
    have hsq : (μ l : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hl))
    split_ifs
    · rw [div_pow, mul_pow, hsq, one_mul]
      field_simp
    · simp
  rw [heq]
  field_simp

theorem upperInverse_explicit {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    upperInverse P y d =
      ∑ r ∈ P.divisors, if d ∣ r then (μ (r / d) : ℝ) * y r else 0 := by
  simp only [upperInverse, mobiusInverse]
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * y (P / b))]
  rw [← upper_divisor_sum hP hd (fun a => (μ ((P / d) / a) : ℝ) * y (P / a))]
  apply Finset.sum_congr rfl
  intro r hr
  have hrP := Nat.dvd_of_mem_divisors hr
  have heq : P / d / (P / r) = r / d := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm d (P / r), ← Nat.div_div_eq_div_mul,
      Nat.div_div_self hrP hP]
  simp only [heq, Nat.div_div_self hrP hP]

theorem target_abs (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) {l : ℕ}
    (hl : l ∈ s.prodPrimes.divisors) :
    |target s z l| = (if l ≤ z then s.selbergTerms l else 0) / mass s z := by
  have hμ : |(μ l : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_mem_divisors_prodPrimes hl)
  rw [target]
  split_ifs
  · rw [abs_div, abs_mul, hμ, one_mul,
      abs_of_pos (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)),
      abs_of_pos (mass_pos s hz)]
  · simp

theorem upperInverse_target_abs_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) :
    |upperInverse s.prodPrimes (target s z) d| ≤ 1 := by
  rw [upperInverse_explicit s.prodPrimes_ne_zero hd]
  calc
    _ ≤ ∑ r ∈ s.prodPrimes.divisors,
        |if d ∣ r then (μ (r / d) : ℝ) * target s z r else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ s.prodPrimes.divisors,
        (if r ≤ z then s.selbergTerms r else 0) / mass s z := by
      apply Finset.sum_le_sum
      intro r hr
      have hnon : 0 ≤ (if r ≤ z then s.selbergTerms r else 0) / mass s z := by
        apply div_nonneg _ (mass_pos s hz).le
        split_ifs
        · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hr)).le
        · exact le_rfl
      by_cases hdr : d ∣ r
      · rw [ite_eq_left hdr, abs_mul, target_abs s hz hr]
        apply mul_le_of_le_one_left hnon
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r / d)
      · simpa only [ite_eq_right hdr, abs_zero] using hnon
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self (mass_pos s hz).ne'

theorem weights_abs_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) : |weights s z d| ≤ (s.nu d)⁻¹ := by
  rw [weights, abs_mul, abs_inv, abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd)]
  exact mul_le_of_le_one_right (inv_pos.mpr (s.nu_pos_of_dvd_prodPrimes hd)).le
    (upperInverse_target_abs_le s hz hd)

theorem weights_zero_above (s : BoundingSieve) {z d : ℕ} (hd : d ∣ s.prodPrimes)
    (hzd : z < d) : weights s z d = 0 := by
  rw [weights, upperInverse_explicit s.prodPrimes_ne_zero hd]
  suffices h : (∑ r ∈ s.prodPrimes.divisors,
      if d ∣ r then (μ (r / d) : ℝ) * target s z r else 0) = 0 by rw [h, mul_zero]
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hdr : d ∣ r
  · have hr0 : 0 < r := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero
      s.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hr))
    have hdle := Nat.le_of_dvd hr0 hdr
    simp only [ite_eq_left hdr, target, ite_eq_right (by omega : ¬r ≤ z), mul_zero]
  · simp only [ite_eq_right hdr]

end OrdinarySelbergWeights

end

end OAI
