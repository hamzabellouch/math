import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Analysis.ParameterTails
import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem m_pos (n : ℕ) : 0 < p.m n := by have := hp.m_ge_100 n; omega

theorem C_pos (n : ℕ) : 0 < p.C n := by
  rw [hp.C_eq n]
  exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hp.L_ge_one n))
    (le_max_left _ _)

theorem real_K_pos (n : ℕ) : 0 < (p.K n : ℝ) := by exact_mod_cast hp.K_pos n

theorem real_K_double (n : ℕ) : 2 * (p.K n : ℝ) ≤ (p.K (n + 1) : ℝ) := by
  exact_mod_cast (hp.K_double n).le

theorem summable_reciprocal : Summable (fun n => 1 / (p.K n : ℝ)) :=
  ParameterTails.summable_reciprocal hp.real_K_pos hp.real_K_double

theorem reciprocal_tail_bound (n : ℕ) :
    (∑' r : ℕ, 1 / (p.K (n + 1 + r) : ℝ)) ≤ 2 / (p.K (n + 1) : ℝ) :=
  ParameterTails.reciprocal_tail_bound hp.real_K_pos hp.real_K_double n

theorem prefix_count_succ_le (n : ℕ) :
    (p.prefixCount (n + 1) : ℝ) ≤ (101 / 100 : ℝ) * p.m n := by
  have h := hp.prefix_count_le n
  simp only [ProductScaleData.prefixCount, Finset.sum_range_succ, Nat.cast_add] at *
  linarith

theorem N_le_square (n : ℕ) : p.N n ≤ (p.m n : ℝ) ^ 2 := by
  have h : (p.K n : ℝ) ≤ p.m n := by exact_mod_cast hp.m_ge_K n
  dsimp [ProductScaleData.N]
  nlinarith [show (0 : ℝ) ≤ p.m n by positivity]

theorem a_bounds (n : ℕ) :
    1 / (p.m n : ℝ) ≤ p.a n ∧ p.a n ≤ 1 / 4 := by
  have hm : 0 < (p.m n : ℝ) := by exact_mod_cast hp.m_pos n
  have hG : (1 : ℝ) ≤ p.G n := by exact_mod_cast hp.G_pos n
  have hlarge : 4 * (p.G n : ℝ) ≤ p.m n := by exact_mod_cast hp.m_ge_G n
  dsimp [ProductScaleData.a]
  constructor
  · exact div_le_div_of_nonneg_right hG hm.le
  · apply (div_le_iff₀ hm).mpr
    linarith

theorem b_bounds (n : ℕ) :
    1 / (p.m n : ℝ) ≤ p.b n ∧ p.b n ≤ 1 / 4 := by
  have hm100 : (100 : ℝ) ≤ p.m n := by exact_mod_cast hp.m_ge_100 n
  have hm1 : (1 : ℝ) ≤ p.m n := by linarith
  have hm : (0 : ℝ) < p.m n := by linarith
  dsimp [ProductScaleData.b]
  constructor
  · rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  · calc
      (p.m n : ℝ) ^ (-(19 / 20 : ℝ)) ≤ (p.m n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = (Real.sqrt (p.m n : ℝ))⁻¹ := by rw [Real.rpow_neg hm.le, ← Real.sqrt_eq_rpow]
      _ ≤ 1 / 4 := by
        have hs : (4 : ℝ) ≤ Real.sqrt (p.m n : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hs

theorem K_strictMono : StrictMono p.K := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := hp.K_double n
  omega

theorem m_lt_next_K (n : ℕ) : p.m n < p.K (n + 1) := by
  have hm : (20 : ℝ) ≤ p.m n := by exact_mod_cast le_trans (by decide) (hp.m_ge_100 n)
  have h := SamplingHorizon.twice_lt_ceiling_cutoff hm
  rw [← hp.next_K n] at h
  have hmpos : (0 : ℝ) < p.m n := by exact_mod_cast hp.m_pos n
  have : (p.m n : ℝ) < p.K (n + 1) := by linarith
  exact_mod_cast this

theorem m_strictMono : StrictMono p.m := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (hp.m_lt_next_K n).trans_le (hp.m_ge_K (n + 1))

theorem N_strictMono : StrictMono p.N := by
  intro n k hnk
  have hm : (p.m n : ℝ) < p.m k := by exact_mod_cast hp.m_strictMono hnk
  have hK : (p.K n : ℝ) < p.K k := by exact_mod_cast hp.K_strictMono hnk
  exact mul_lt_mul hm hK.le (hp.real_K_pos n) (by positivity)

theorem K_ge_100 (n : ℕ) : 100 ≤ p.K n := by
  simpa only [hp.initial_K] using hp.K_strictMono.monotone (Nat.zero_le n)

theorem m_ge_pow_self (n : ℕ) : 2 ^ n ≤ p.m n := by
  have h := hp.m_ge_pow n
  have hpow : 2 ^ n ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  exact hpow.trans h

theorem reciprocal_sum_le : (∑' n, 1 / (p.K n : ℝ)) ≤ 1 / 50 := by
  have h := ParameterTails.tsum_tail_le_of_half_decay
    (fun n => (one_div_pos.mpr (hp.real_K_pos n)).le)
    (ParameterTails.reciprocal_half_decay hp.real_K_pos hp.real_K_double) 0
  norm_num [hp.initial_K] at h ⊢
  exact h

theorem prefixCost_nonneg (n : ℕ) : 0 ≤ p.prefixCost n := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (hp.C_pos r).le (Nat.cast_nonneg _)

theorem coefficientBound_ge_one (n : ℕ) : 1 ≤ p.coefficientBound n := by
  apply Real.one_le_exp_iff.mpr
  exact mul_nonneg (by positivity) (hp.prefixCost_nonneg n)

theorem one_le_C_div_K (n : ℕ) : 1 ≤ p.C n / p.K n := by
  have hK : (1 : ℝ) ≤ p.K n := by exact_mod_cast hp.K_pos n
  have hC : (p.K n : ℝ) ^ 2 ≤ p.C n := by rw [hp.C_eq n]; exact le_max_right _ _
  apply (le_div_iff₀ (hp.real_K_pos n)).mpr
  nlinarith

end Invariant233.ProductScaleLaws

end

end OAI
