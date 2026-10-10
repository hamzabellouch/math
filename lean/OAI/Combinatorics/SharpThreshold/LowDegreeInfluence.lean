import Mathlib

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Summing pivotal-event three-halves powers using a uniform influence bound. -/
theorem sum_mul_sqrt_le {ι : Type u} [Fintype ι] (a : ι → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : ∀ i, a i ≤ B) :
    (∑ i, a i * Real.sqrt (a i)) ≤ Real.sqrt B * ∑ i, a i := by
  calc
    (∑ i, a i * Real.sqrt (a i)) ≤ ∑ i, a i * Real.sqrt B := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hB i)) (ha i)
    _ = Real.sqrt B * ∑ i, a i := by rw [Finset.mul_sum]; congr 1; ext i; ring

/-- A convenient conversion between real three-halves powers and square roots. -/
theorem rpow_three_halves_eq_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3/2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_add_of_nonneg hx (show (0:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) using 1 <;> norm_num

/-- The small-total-influence regime turns the individual influence bound into a power of `m`. -/
theorem sqrt_influence_ratio_le (m I : ℝ) (hm : 0 < m)
    (hI : I ≤ m ^ (1/4 : ℝ)) :
    Real.sqrt (I/m) ≤ m ^ (-3/8 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Real.rpow_nonneg hm.le _, ?_⟩
  have hsq : (m ^ (-3/8 : ℝ))^2 = m ^ (-3/4 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm.le]
    norm_num
  rw [hsq]
  calc
    I/m ≤ m ^ (1/4 : ℝ) / m := div_le_div_of_nonneg_right hI hm.le
    _ = m ^ (-3/4 : ℝ) := by
      convert (Real.rpow_sub hm (1/4 : ℝ) 1).symm using 1 <;> norm_num

/-- The numerical case split at the end of the low-degree Fourier estimate.
The factor `A` can be instantiated with `σ²`. -/
theorem low_degree_influence_bound {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hL1 : L ≤ 1)
    (hprojection : L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hI0 : 0 ≤ I := by rw [← hsum]; exact Finset.sum_nonneg fun i _ => ha i
  have hpow0 : 0 ≤ m ^ (1/16 : ℝ) := Real.rpow_nonneg hmpos.le _
  by_cases hsmall : I ≤ m ^ (1/4 : ℝ)
  · have hsum_bound : (∑ i, (a i) ^ (3/2 : ℝ)) ≤ m ^ (-3/8 : ℝ) * I := by
      calc
        (∑ i, (a i) ^ (3/2 : ℝ)) = ∑ i, a i * Real.sqrt (a i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact rpow_three_halves_eq_mul_sqrt (a i) (ha i)
        _ ≤ Real.sqrt (I/m) * I := by
          simpa [hsum] using sum_mul_sqrt_le a (I/m) ha hindividual
        _ ≤ m ^ (-3/8 : ℝ) * I := mul_le_mul_of_nonneg_right
          (sqrt_influence_ratio_le m I hmpos hsmall) hI0
    have hcoefficient : A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) ≤ m ^ (-1/4 : ℝ) := by
      calc
        A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) ≤
            m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using mul_le_mul_of_nonneg_right hA1 hpow0)
            (Real.rpow_nonneg hmpos.le _)
        _ = m ^ (-5/16 : ℝ) := by rw [← Real.rpow_add hmpos]; norm_num
        _ ≤ m ^ (-1/4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
    calc
      L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ) := hprojection
      _ ≤ A * m ^ (1/16 : ℝ) * (m ^ (-3/8 : ℝ) * I) :=
        mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg hA0 hpow0)
      _ = (A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ)) * I := by ring
      _ ≤ m ^ (-1/4 : ℝ) * I := mul_le_mul_of_nonneg_right hcoefficient hI0
  · have hinverse : m ^ (-1/4 : ℝ) * m ^ (1/4 : ℝ) = 1 := by
      rw [← Real.rpow_add hmpos]
      norm_num
    calc
      L ≤ 1 := hL1
      _ = m ^ (-1/4 : ℝ) * m ^ (1/4 : ℝ) := hinverse.symm
      _ ≤ m ^ (-1/4 : ℝ) * I := mul_le_mul_of_nonneg_left
        (le_of_lt (lt_of_not_ge hsmall)) (Real.rpow_nonneg hmpos.le _)

/-- Version accepting the hypercontractive factor before its power bound is substituted. -/
theorem low_degree_influence_bound_of_factor {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A R L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hR : R ≤ m ^ (1/16 : ℝ)) (hL1 : L ≤ 1)
    (hprojection : L ≤ A * R * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  apply low_degree_influence_bound a m I A L hm ha hsum hindividual hA0 hA1 hL1
  exact hprojection.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR hA0)
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _))

end Problem313

end

end OAI
