import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstTailNormalization

namespace OAI

/-! # Uniform cutoff geometry for the actual common-divisor pair family -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_pair_product_bound {N D : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) :
    0 < D ∧ D ≤ N ∧ D ^ 2 * quadraticPairKernel z.1 z.2 ≤ N ^ 2 := by
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hsR := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
  have htR := Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
  refine ⟨hg ▸ Nat.gcd_pos_of_pos_left _ hsR.1,
    hg ▸ (Nat.gcd_le_left _ hsR.1).trans hsR.2, ?_⟩
  rw [← hg, quadraticPairKernel_factor, pow_two]
  exact Nat.mul_le_mul hsR.2 htR.2

theorem quadratic_pair_tail_scales {N D e : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) (he : e ∈ (2 * D).divisors) :
    0 < e ∧ e * quadraticPairKernel z.1 z.2 ≤ 2 * N ^ 2 ∧
      quadraticPairKernel z.1 z.2 ≤ N ^ 2 := by
  obtain ⟨hD, _, hp⟩ := quadratic_pair_product_bound hz
  have hepos := Nat.pos_of_mem_divisors he
  have heD := Nat.le_of_dvd (show 0 < 2 * D by omega) (Nat.dvd_of_mem_divisors he)
  have hDsq : D ≤ D ^ 2 := by nlinarith
  have hq : quadraticPairKernel z.1 z.2 ≤ D ^ 2 * quadraticPairKernel z.1 z.2 :=
    Nat.le_mul_of_pos_left _ (pow_pos hD 2)
  refine ⟨hepos, ?_, hq.trans hp⟩
  calc
    _ ≤ (2 * D) * quadraticPairKernel z.1 z.2 := Nat.mul_le_mul_right _ heD
    _ ≤ 2 * (D ^ 2 * quadraticPairKernel z.1 z.2) := by nlinarith [Nat.mul_le_mul_right (quadraticPairKernel z.1 z.2) hDsq]
    _ ≤ 2 * N ^ 2 := Nat.mul_le_mul_left 2 hp

theorem quadratic_pair_normalized_tail_scale {N D e : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) (he : e ∈ (2 * D).divisors) :
    (e : ℝ) * quadraticPairKernel z.1 z.2 * Real.sqrt (quadraticPairKernel z.1 z.2) ≤
      2 * (N : ℝ) ^ 3 := by
  obtain ⟨_, heq, hq⟩ := quadratic_pair_tail_scales hz he
  have heqR : (e : ℝ) * quadraticPairKernel z.1 z.2 ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast heq
  have hqR : (quadraticPairKernel z.1 z.2 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hq
  have hs : Real.sqrt (quadraticPairKernel z.1 z.2) ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (quadraticPairKernel z.1 z.2)),
      Real.sqrt_nonneg (quadraticPairKernel z.1 z.2), Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ (2 * (N : ℝ) ^ 2) * N := mul_le_mul heqR hs (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

theorem quadratic_pair_first_cutoff {N D e K : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs N D) (he : e ∈ (2 * D).divisors)
    {M J : ℝ} (hJ : 0 ≤ J)
    (hcut : 2 * (N : ℝ) ^ 2 * J ≤ M * ((K : ℝ) + 1)) :
    J ≤ (M / ((e : ℝ) * quadraticPairKernel z.1 z.2)) * ((K : ℝ) + 1) := by
  obtain ⟨hepos, heq, _⟩ := quadratic_pair_tail_scales hz he
  have hz' := (Finset.mem_filter.mp hz).1
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hqpos := Nat.pos_of_ne_zero (quadraticPairKernel_squarefree
    (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).ne_zero
  have hden : 0 < (e : ℝ) * quadraticPairKernel z.1 z.2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  apply le_trans _ hcut
  have hh : (e : ℝ) * quadraticPairKernel z.1 z.2 ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast heq
  nlinarith [mul_le_mul_of_nonneg_left hh hJ]

end Ostmann

end OAI
