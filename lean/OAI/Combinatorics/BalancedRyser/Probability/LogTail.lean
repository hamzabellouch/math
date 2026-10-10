import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace OAI

open Filter Topology

namespace BalancedRyser

theorem polynomial_mul_ratio_pow_le_inv
    (q r B : ℕ) (C : ℝ) (hq : 0 < q) (hBpos : 0 < B)
    (hC : 0 ≤ C) (hlog : Real.log (q : ℝ) ≤ (B : ℝ))
    (hlarge : C * Real.exp ((r : ℝ) + 1) ≤ (B : ℝ)) :
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B ≤ (q : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hbase : C / (B : ℝ) ≤ Real.exp (-((r : ℝ) + 1)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hBR).2
    simpa [div_eq_mul_inv, mul_comm] using
      ((le_div_iff₀ (Real.exp_pos ((r : ℝ) + 1))).2 hlarge)
  have hpow : (C / (B : ℝ)) ^ B ≤
      Real.exp (-((r : ℝ) + 1)) ^ B :=
    pow_le_pow_left₀ (div_nonneg hC hBR.le) hbase B
  calc
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B
        ≤ (q : ℝ) ^ r * Real.exp (-((r : ℝ) + 1)) ^ B :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hqR.le _)
    _ = Real.exp ((r : ℝ) * Real.log (q : ℝ) - ((r : ℝ) + 1) * B) := by
      have hqpow : (q : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hqR]
      rw [hqpow, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log (q : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    _ = (q : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hqR]

theorem tendsto_log_cutoff_atTop :
    Tendsto (fun q : ℕ => Nat.ceil (Real.log (q : ℝ))) atTop atTop :=
  tendsto_nat_ceil_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_polynomial_mul_cutoff_tail
    (B : ℕ → ℕ)
    (hlog : ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (B q : ℝ))
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r * (C / (B q : ℝ)) ^ B q)
      atTop (𝓝 0) := by
  have hcut : Tendsto (fun q : ℕ => (B q : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ hlog
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun q =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg q) r)
        (pow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _))
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
      hcut.eventually (eventually_gt_atTop 0),
      hcut.eventually (eventually_ge_atTop (C * Real.exp ((r : ℝ) + 1)))]
      with q hq hlogq hB hlarge
    exact polynomial_mul_ratio_pow_le_inv q r _ C hq
      (by exact_mod_cast hB) hC hlogq hlarge
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem tendsto_polynomial_mul_log_cutoff_tail
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (C / (Nat.ceil (Real.log (q : ℝ)) : ℝ)) ^
          Nat.ceil (Real.log (q : ℝ))) atTop (𝓝 0) :=
  tendsto_polynomial_mul_cutoff_tail _
    (Filter.Eventually.of_forall (fun _ => Nat.le_ceil _)) r C hC

theorem tendsto_large_pencil_union_bound (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ 2 *
        (C / (Nat.ceil (Real.log (q : ℝ)) : ℝ)) ^
          Nat.ceil (Real.log (q : ℝ))) atTop (𝓝 0) :=
  tendsto_polynomial_mul_log_cutoff_tail 2 C hC

theorem choose_le_exp_mul_div_pow (n B : ℕ) (hB : 0 < B) :
    (n.choose B : ℝ) ≤ (Real.exp 1 * n / B) ^ B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hf : (0 : ℝ) < B.factorial := by
    exact_mod_cast Nat.factorial_pos B
  have hseries := Real.pow_div_factorial_le_exp (B : ℝ) hBR.le B
  have hinv : 1 / (B.factorial : ℝ) ≤ (Real.exp 1 / B) ^ B := by
    rw [div_pow, Real.exp_one_pow]
    apply (div_le_div_iff₀ hf (pow_pos hBR B)).2
    simpa using (div_le_iff₀ hf).1 hseries
  calc
    (n.choose B : ℝ) ≤ (n : ℝ) ^ B / B.factorial := Nat.choose_le_pow_div B n
    _ = (n : ℝ) ^ B * (1 / (B.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ B * (Real.exp 1 / B) ^ B :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg (Nat.cast_nonneg n) B)
    _ = (Real.exp 1 * n / B) ^ B := by rw [← mul_pow]; congr 1; ring

theorem slot_choose_mul_pow_le
    (q B : ℕ) (K : ℝ) (hq : 0 < q) (hB : 0 < B) (hK : 0 ≤ K) :
    ((2 * (q + 1)).choose B : ℝ) * (K / (q : ℝ)) ^ B ≤
      (4 * Real.exp 1 * K / (B : ℝ)) ^ B := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    ((2 * (q + 1)).choose B : ℝ) * (K / (q : ℝ)) ^ B
        ≤ (Real.exp 1 * (2 * (q + 1) : ℕ) / B) ^ B * (K / (q : ℝ)) ^ B :=
      mul_le_mul_of_nonneg_right (choose_le_exp_mul_div_pow _ B hB)
        (pow_nonneg (div_nonneg hK hqR.le) B)
    _ = (Real.exp 1 * (2 * (q + 1) : ℕ) / B * (K / (q : ℝ))) ^ B := by
      rw [mul_pow]
    _ ≤ (4 * Real.exp 1 * K / (B : ℝ)) ^ B := by
      apply pow_le_pow_left₀ (by positivity)
      have hratio : (2 * (q + 1) : ℕ) / (q : ℝ) ≤ 4 := by
        apply (div_le_iff₀ hqR).2
        push_cast
        linarith
      have hmul := mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (Real.exp_pos 1).le hK)
      have hdiv := div_le_div_of_nonneg_right hmul hBR.le
      convert hdiv using 1 <;> ring

theorem tendsto_polynomial_mul_slot_choose_tail
    (r : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (((2 * (q + 1)).choose (Nat.ceil (Real.log (q : ℝ))) : ℝ) *
          (K / (q : ℝ)) ^ Nat.ceil (Real.log (q : ℝ))))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_polynomial_mul_log_cutoff_tail r (4 * Real.exp 1 * K) (by positivity))
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      tendsto_log_cutoff_atTop.eventually (eventually_gt_atTop 0)] with q hq hB
    exact mul_le_mul_of_nonneg_left (slot_choose_mul_pow_le q _ K hq hB hK)
      (pow_nonneg (Nat.cast_nonneg q) r)

theorem choose_le_pow_mul_exp_div (n m q : ℕ) (hq : 0 < q) :
    (n.choose m : ℝ) ≤ (q : ℝ) ^ m * Real.exp ((n : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht := Real.pow_div_factorial_le_exp ((n : ℝ) / q)
    (div_nonneg (Nat.cast_nonneg n) hqR.le) m
  calc
    (n.choose m : ℝ) ≤ (n : ℝ) ^ m / m.factorial := Nat.choose_le_pow_div m n
    _ = (q : ℝ) ^ m * (((n : ℝ) / q) ^ m / m.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ (q : ℝ) ^ m * Real.exp ((n : ℝ) / q) :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg hqR.le m)

theorem affine_line_subset_count_le (q m : ℕ) (hq : 0 < q) :
    ((q * (q + 1)).choose m : ℝ) ≤ (q : ℝ) ^ m * Real.exp (2 * q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hratio : ((q * (q + 1) : ℕ) : ℝ) / q ≤ 2 * q := by
    push_cast
    rw [mul_div_cancel_left₀ ((q : ℝ) + 1) hqR.ne']
    linarith
  exact (choose_le_pow_mul_exp_div (q * (q + 1)) m q hq).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hratio) (pow_nonneg hqR.le m))

theorem eventually_log_le_power_cutoff (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ q : ℕ in atTop,
      Real.log (q : ℝ) ≤ (Nat.floor ((q : ℝ) ^ β) + 1 : ℕ) := by
  have hs : ∀ᶠ q : ℕ in atTop,
      ‖Real.log (q : ℝ)‖ ≤ ‖(q : ℝ) ^ β‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (isLittleO_log_rpow_atTop hβ).eventuallyLE
  filter_upwards [hs, eventually_ge_atTop (1 : ℕ)] with q hq hq1
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  rw [Real.norm_of_nonneg (Real.log_nonneg hqR),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) β)] at hq
  simpa only [Nat.cast_add, Nat.cast_one] using
    hq.trans (Nat.lt_floor_add_one ((q : ℝ) ^ β)).le

theorem tendsto_polynomial_mul_power_cutoff_tail
    (β : ℝ) (hβ : 0 < β) (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (C / (Nat.floor ((q : ℝ) ^ β) + 1 : ℕ)) ^
          (Nat.floor ((q : ℝ) ^ β) + 1)) atTop (𝓝 0) :=
  tendsto_polynomial_mul_cutoff_tail _
    (eventually_log_le_power_cutoff β hβ) r C hC

end BalancedRyser

end OAI
