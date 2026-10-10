import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology BigOperators

namespace Balanced.LocalAsymptotics

theorem summable_polynomial_mul_pow_div_factorial (a : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Summable (fun b : ℕ => (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) := by
  apply (Real.summable_pow_div_factorial (2 * C)).of_norm_bounded_eventually_nat
  have h := (tendsto_pow_const_div_const_pow_of_one_lt a (by norm_num : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with b hb
  have hb' : (b : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
    exact le_of_lt ((div_lt_one (by positivity : (0 : ℝ) < 2 ^ b)).mp hb)
  rw [Real.norm_of_nonneg (by positivity), mul_pow]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb' (pow_nonneg hC b))
    (by positivity)

theorem tendsto_log_pow_div (a : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ a / x) atTop (𝓝 0) := by
  have h := isLittleO_log_rpow_rpow_atTop (a : ℝ) (by norm_num : (0 : ℝ) < 1)
  simpa only [Real.rpow_natCast, Real.rpow_one] using h.tendsto_div_nhds_zero

theorem tendsto_ceil_log_pow_div (a : ℕ) :
    Tendsto (fun x : ℝ => (⌈Real.log x⌉₊ : ℝ) ^ a / x) atTop (𝓝 0) := by
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hx : ∀ᶠ x : ℝ in atTop, 0 ≤ x := eventually_ge_atTop 0
  apply squeeze_zero' (hx.mono fun x hx => by positivity)
    (g := fun x : ℝ => (2 : ℝ) ^ a * ((Real.log x) ^ a / x))
  · filter_upwards [hlog, hx] with x hlog hx
    have hceil : (⌈Real.log x⌉₊ : ℝ) ≤ 2 * Real.log x := by
      have h := Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
      linarith
    calc
      (⌈Real.log x⌉₊ : ℝ) ^ a / x ≤ (2 * Real.log x) ^ a / x := by gcongr
      _ = (2 : ℝ) ^ a * ((Real.log x) ^ a / x) := by rw [mul_pow]; ring
  · simpa using (tendsto_log_pow_div a).const_mul ((2 : ℝ) ^ a)

theorem tendsto_ceil_log_cube_div_nat :
    Tendsto (fun q : ℕ => (⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ))
      atTop (𝓝 0) :=
  (tendsto_ceil_log_pow_div 3).comp tendsto_natCast_atTop_atTop

theorem large_pencil_tail_le_inv (C x : ℝ) (hC : 0 ≤ C) (hx : 0 < x)
    (hlog : 1 ≤ Real.log x)
    (hlarge : C * Real.exp 3 ≤ (⌈Real.log x⌉₊ : ℝ)) :
    x ^ 2 * (C / (⌈Real.log x⌉₊ : ℝ)) ^ ⌈Real.log x⌉₊ ≤ x⁻¹ := by
  have hceil := Nat.le_ceil (Real.log x)
  have hB : (0 : ℝ) < (⌈Real.log x⌉₊ : ℝ) := by linarith
  have hratio : C / (⌈Real.log x⌉₊ : ℝ) ≤ Real.exp (-3) := by
    apply (div_le_iff₀ hB).2
    calc
      C = (C * Real.exp 3) * Real.exp (-3) := by
        rw [mul_assoc, ← Real.exp_add]
        norm_num
      _ ≤ (⌈Real.log x⌉₊ : ℝ) * Real.exp (-3) :=
        mul_le_mul_of_nonneg_right hlarge (Real.exp_pos _).le
      _ = Real.exp (-3) * (⌈Real.log x⌉₊ : ℝ) := mul_comm _ _
  have hexp : Real.exp (-3 * Real.log x) = (x ^ 3)⁻¹ := by
    rw [show -3 * Real.log x = -(3 * Real.log x) by ring, Real.exp_neg]
    congr 1
    simpa [Real.exp_log hx] using Real.exp_nat_mul (Real.log x) 3
  calc
    x ^ 2 * (C / (⌈Real.log x⌉₊ : ℝ)) ^ ⌈Real.log x⌉₊
        ≤ x ^ 2 * Real.exp (-3) ^ ⌈Real.log x⌉₊ := by gcongr
    _ = x ^ 2 * Real.exp (-3 * (⌈Real.log x⌉₊ : ℝ)) := by
      rw [mul_comm (-3), Real.exp_nat_mul]
    _ ≤ x ^ 2 * Real.exp (-3 * Real.log x) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
      apply Real.exp_le_exp.mpr
      linarith
    _ = x⁻¹ := by rw [hexp]; field_simp

theorem tendsto_large_pencil_tail (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun x : ℝ => x ^ 2 *
      (C / (⌈Real.log x⌉₊ : ℝ)) ^ ⌈Real.log x⌉₊) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun x => by positivity)
    (g := fun x : ℝ => x⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually_ge_atTop (C * Real.exp 3)] with x hx hlog hlarge
    exact large_pencil_tail_le_inv C x hC hx hlog
      (hlarge.trans (Nat.le_ceil (Real.log x)))
  · exact tendsto_inv_atTop_zero

theorem tendsto_large_pencil_tail_nat (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 2 *
      (C / (⌈Real.log (q : ℝ)⌉₊ : ℝ)) ^ ⌈Real.log (q : ℝ)⌉₊)
      atTop (𝓝 0) :=
  (tendsto_large_pencil_tail C hC).comp tendsto_natCast_atTop_atTop

theorem sum_polynomial_mul_pow_div_factorial_le (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (s : Finset ℕ) :
    (∑ b ∈ s, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) ≤
      ∑' b : ℕ, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ) := by
  exact (summable_polynomial_mul_pow_div_factorial a C hC).sum_le_tsum s
    (fun b _ => by positivity)

theorem tendsto_weighted_log_bound (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (s : ℕ → Finset ℕ) :
    Tendsto (fun q : ℕ =>
      (∑ b ∈ s q, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) *
      ((⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero (fun q => by positivity)
    (g := fun q : ℕ => (∑' b : ℕ, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) *
      ((⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ)))
  · intro q
    apply mul_le_mul_of_nonneg_right
      (sum_polynomial_mul_pow_div_factorial_le a C hC (s q))
    positivity
  · simpa using tendsto_ceil_log_cube_div_nat.const_mul
      (∑' b : ℕ, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ))

theorem tendsto_plane_weighted_pencil_sum (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (s : ℕ → Finset ℕ) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 2 *
      ∑ b ∈ s q, ((b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) *
        ((⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ) ^ 3)) atTop (𝓝 0) := by
  apply (tendsto_weighted_log_bound a C hC s).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [← Finset.sum_mul]
  field_simp

theorem pencil_common_factor_le (q K : ℝ) (b κ : ℕ)
    (hq : 1 ≤ q) (hK : 0 ≤ K) (hκ : κ ≤ 5 * b) :
    (32 : ℝ) ^ b * (q + 1) ^ (5 * b - κ) * (K / q) ^ b / q ^ (4 * b) ≤
      (1024 * K) ^ b / q ^ κ := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hp : (q + 1) ^ (5 * b - κ) ≤ (2 : ℝ) ^ (5 * b) * q ^ (5 * b - κ) := by
    calc
      (q + 1) ^ (5 * b - κ) ≤ (2 * q) ^ (5 * b - κ) := by gcongr; linarith
      _ = (2 : ℝ) ^ (5 * b - κ) * q ^ (5 * b - κ) := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ (5 * b) * q ^ (5 * b - κ) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
          (pow_nonneg hqpos.le _)
  have hqp : q ^ (5 * b) = q ^ b * q ^ (4 * b) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : (32 : ℝ) ^ b * (2 : ℝ) ^ (5 * b) * K ^ b = (1024 * K) ^ b := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    norm_num
  calc
    (32 : ℝ) ^ b * (q + 1) ^ (5 * b - κ) * (K / q) ^ b / q ^ (4 * b)
        ≤ (32 : ℝ) ^ b * ((2 : ℝ) ^ (5 * b) * q ^ (5 * b - κ)) *
          (K / q) ^ b / q ^ (4 * b) := by gcongr
    _ = (1024 * K) ^ b / q ^ κ := by
      rw [div_pow, pow_sub₀ q hqne hκ, hqp]
      field_simp
      nlinarith [hc]

end Balanced.LocalAsymptotics

end OAI
