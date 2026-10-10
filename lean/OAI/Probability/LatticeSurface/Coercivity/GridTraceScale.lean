import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

end GridTrace

namespace GridTrace

lemma kernel_scale (p q α C N s : ℝ) (hpq : p.HolderConjugate q)
    (hC : 0 < C) (hN : 0 < N) (hs : 0 < s) :
    ((4/s)*C*((5*s)/N)^α)^(1/p)*(128*C*s)^(1/q) =
      ((4*C*5^α)^(1/p)*(128*C)^(1/q))*N^(-α/p)*s^(1+(α-2)/p) := by
  have hid : (4/s)*C*((5*s)/N)^α = (4*C*5^α)*N^(-α)*s^(α-1) := by
    rw [Real.div_rpow (by positivity) hN.le,Real.mul_rpow (by norm_num) hs.le,
      Real.rpow_neg hN.le,Real.rpow_sub hs]
    rw [Real.rpow_one]
    field_simp
  rw [hid,Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hs.le,
    ← Real.rpow_mul hN.le,← Real.rpow_mul hs.le]
  have hcomb : s^((α-1)*(1/p))*s^(1/q)=s^(1+(α-2)/p) := by
    rw [← Real.rpow_add hs]
    congr 1
    have hh := hpq.inv_add_inv_eq_one
    rw [← one_div,← one_div] at hh
    field_simp [hpq.ne_zero,hpq.symm.ne_zero] at hh ⊢
    nlinarith
  calc
    _ = ((4*C*5^α)^(1/p)*(128*C)^(1/q))*N^((-α)*(1/p))*
        (s^((α-1)*(1/p))*s^(1/q)) := by ring
    _ = _ := by rw [hcomb];congr 2;congr 1;ring

lemma dyadic_global_scale (p α N : ℝ) (hp : 0 < p) (hα : 2-p < α)
    (hN : 0 < N) (M : ℕ) (hM : (2:ℝ)^M ≤ 2*N) :
    N^(-α/p)*(∑ k ∈ Finset.range M, ((2:ℝ)^k)^(1+(α-2)/p)) ≤
      ((2:ℝ)^(1+(α-2)/p)/((2:ℝ)^(1+(α-2)/p)-1))*N^(1-2/p) := by
  let β := 1+(α-2)/p
  have hβ : 0 < β := by dsimp [β];apply (neg_lt_iff_pos_add').mp;apply (lt_div_iff₀ hp).mpr;linarith
  have hden : 0 < (2:ℝ)^β-1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ)
  calc
    _ ≤ N^(-α/p)*(((2:ℝ)^M)^β/((2:ℝ)^β-1)) :=
      mul_le_mul_of_nonneg_left (dyadic_sum_bound β hβ M) (Real.rpow_nonneg hN.le _)
    _ ≤ N^(-α/p)*((2*N)^β/((2:ℝ)^β-1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hM hβ.le) hden.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hN.le]
      have he : N^(-α/p)*N^β = N^(1-2/p) := by
        rw [← Real.rpow_add hN]
        congr 1
        dsimp [β]
        ring
      calc
        _ = ((2:ℝ)^β/((2:ℝ)^β-1))*(N^(-α/p)*N^β) := by ring
        _ = _ := by rw [he]

end GridTrace

end

end OAI
