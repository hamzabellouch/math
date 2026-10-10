import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.SamplingAsymptotics

theorem tendsto_pow_self_of_tendsto_zero {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n) (hlim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (a n) ^ n) atTop (𝓝 0) := by
  have hu : ∀ᶠ n in atTop, a n ≤ (1 / 2 : ℝ) :=
    hlim.eventually_le_const (by norm_num)
  apply squeeze_zero' _ _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
  · filter_upwards [ha] with n hn using pow_nonneg hn n
  · filter_upwards [ha, hu] with n hn hnu
    exact pow_le_pow_left₀ hn hnu n

theorem tendsto_logarithmic_diagonal (C a b : ℝ) (hC : 0 ≤ C) (hab : a < b) :
    Tendsto (fun n : ℕ =>
      (C * (n : ℝ) ^ a * Real.log n) ^ n / (n : ℝ) ^ (b * n))
      atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun n => C * Real.log n / (n : ℝ) ^ (b - a)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [r, mul_div_assoc] using h.const_mul C
  have hrnonneg : ∀ᶠ n in atTop, 0 ≤ r n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg hC (Real.log_nonneg hnreal))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  apply (tendsto_pow_self_of_tendsto_zero hrnonneg hr).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_mul_natCast hnpos.le, ← div_pow]
  congr 1
  dsimp [r]
  rw [Real.rpow_sub hnpos]
  field_simp

theorem tendsto_source_diagonal :
    Tendsto (fun n : ℕ =>
      (8 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n) ^ n /
        (n : ℝ) ^ ((69 / 100 : ℝ) * n)) atTop (𝓝 0) :=
  tendsto_logarithmic_diagonal 8 (3 / 5) (69 / 100) (by norm_num) (by norm_num)

theorem tendsto_dimension_mul_rpow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-r)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change (n : ℝ) ^ (-(r - 1)) = _
  rw [show -(r - 1) = 1 + -r by ring, Real.rpow_add hnpos, Real.rpow_one]

theorem tendsto_one_add_pow {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 + a n) ^ n) atTop (𝓝 1) := by
  have he : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * a n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards [ha] with n hn
    exact one_le_pow₀ (by linarith : 1 ≤ 1 + a n)
  · filter_upwards [ha] with n hn
    calc
      (1 + a n) ^ n ≤ (Real.exp (a n)) ^ n :=
        pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp (a n)) n
      _ = Real.exp ((n : ℝ) * a n) := (Real.exp_nat_mul _ _).symm

theorem tendsto_one_sub_pow {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, a n ∈ Set.Icc 0 1)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 - a n) ^ n) atTop (𝓝 1) := by
  have hl : Tendsto (fun n : ℕ => 1 - (n : ℝ) * a n) atTop (𝓝 1) := by
    simpa using hlim.const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [ha] with n hn
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (show (-2 : ℝ) ≤ -a n by linarith [hn.2]) n)
  · filter_upwards [ha] with n hn
    exact pow_le_one₀ (sub_nonneg.mpr hn.2) (by linarith [hn.1])

theorem tendsto_one_add_pow_pred {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 + a n) ^ (n - 1)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_one_add_pow ha hlim)
  · filter_upwards [ha] with n hn
    exact one_le_pow₀ (by linarith : 1 ≤ 1 + a n)
  · filter_upwards [ha] with n hn
    exact pow_le_pow_right₀ (by linarith : 1 ≤ 1 + a n) (Nat.sub_le n 1)

theorem eventually_mem_unit_of_dimension_small {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, a n ∈ Set.Icc 0 1 := by
  have hu := hlim.eventually_le_const (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [ha, hu, eventually_ge_atTop (1 : ℕ)] with n hn hnu hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  exact ⟨hn, by nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) hn]⟩

def momentBase (n : ℕ) : ℝ := 1 + 4 * (n : ℝ) ^ (-(6 / 5 : ℝ))

def kernelMass (n : ℕ) : ℝ := 1 - 2 * (n : ℝ) ^ (-(2 : ℝ))

def productError (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (C * (n : ℝ) ^ (-(50 : ℝ))) *
    (momentBase n + C * (n : ℝ) ^ (-(50 : ℝ))) ^ (n - 1)

def diagonalError (n : ℕ) : ℝ :=
  (8 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n) ^ n /
    (n : ℝ) ^ ((69 / 100 : ℝ) * n)

def idealError (n : ℕ) : ℝ := (momentBase n) ^ n - 2 * (kernelMass n) ^ n + 1

def meanSquareBound (C : ℝ) (n : ℕ) : ℝ :=
  2 * (diagonalError n + 3 * productError C n) + 2 * idealError n

theorem tendsto_momentBase_pow :
    Tendsto (fun n => (momentBase n) ^ n) atTop (𝓝 1) := by
  apply tendsto_one_add_pow (Eventually.of_forall fun n => by positivity)
  simpa only [mul_left_comm, mul_zero] using
    (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 6 / 5)).const_mul 4

theorem tendsto_kernelMass_pow :
    Tendsto (fun n => (kernelMass n) ^ n) atTop (𝓝 1) := by
  have hn : ∀ᶠ n : ℕ in atTop, 0 ≤ 2 * (n : ℝ) ^ (-(2 : ℝ)) :=
    Eventually.of_forall fun n => by positivity
  have hl : Tendsto (fun n : ℕ => (n : ℝ) * (2 * (n : ℝ) ^ (-(2 : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_left_comm, mul_zero] using
      (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 2)).const_mul 2
  exact tendsto_one_sub_pow (eventually_mem_unit_of_dimension_small hn hl) hl

theorem tendsto_idealError : Tendsto idealError atTop (𝓝 0) := by
  change Tendsto (fun n => (momentBase n) ^ n - 2 * (kernelMass n) ^ n + 1)
    atTop (𝓝 0)
  convert
    (tendsto_momentBase_pow.sub (tendsto_kernelMass_pow.const_mul 2)).add_const 1
    using 1
  norm_num

theorem tendsto_productError (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (productError C) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n =>
    4 * (n : ℝ) ^ (-(6 / 5 : ℝ)) + C * (n : ℝ) ^ (-(50 : ℝ))
  have ha : ∀ᶠ n in atTop, 0 ≤ a n :=
    Eventually.of_forall fun n => by dsimp [a]; positivity
  have hfirst := (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 6 / 5)).const_mul 4
  have hsecond := (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 50)).const_mul C
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0) := by
    simpa only [a, mul_add, mul_left_comm, mul_zero, add_zero] using hfirst.add hsecond
  have hp := tendsto_one_add_pow_pred ha hlim
  have he : Tendsto (fun n : ℕ => (n : ℝ) * (C * (n : ℝ) ^ (-(50 : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_left_comm, mul_zero] using hsecond
  change Tendsto (fun n : ℕ => (n : ℝ) * (C * (n : ℝ) ^ (-(50 : ℝ))) *
    (momentBase n + C * (n : ℝ) ^ (-(50 : ℝ))) ^ (n - 1)) atTop (𝓝 0)
  simpa only [momentBase, a, add_assoc, zero_mul] using he.mul hp

theorem tendsto_meanSquareBound (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (meanSquareBound C) atTop (𝓝 0) := by
  have hd : Tendsto diagonalError atTop (𝓝 0) := tendsto_source_diagonal
  change Tendsto (fun n => 2 * (diagonalError n + 3 * productError C n) +
    2 * idealError n) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using
    ((hd.add ((tendsto_productError C hC).const_mul 3)).const_mul 2).add
      (tendsto_idealError.const_mul 2)

end Invariant233.SamplingAsymptotics

end

end OAI
