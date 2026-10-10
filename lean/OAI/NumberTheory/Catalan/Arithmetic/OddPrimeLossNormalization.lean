import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Real.Sqrt
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLoss
import OAI.NumberTheory.Catalan.Estimates.TwoAdicQuadratic
import OAI.NumberTheory.Catalan.PrimeLimits.ContinuousWeightedPNT
import OAI.NumberTheory.Catalan.PrimeLimits.ImportedPNTCoreBridge

namespace OAI

section

open Filter
open scoped Topology BigOperators
open Zeta5.Workers.W14
open Zeta5.W12.ImportedPNTCoreBridge

namespace InternalCatalan

theorem oddPrimeLoss_weighted_0_25 (R : ℝ) (hR : 0 < R) :
    weightedPrimeIntervalSum oddPrimeLoss 0 25 R =
      96 * (Chebyshev.theta (25 * R) / R) := by
  have hconstant : weightedPrimeIntervalSum oddPrimeLoss 0 25 R =
      weightedPrimeIntervalSum (fun _ => 96) 0 25 R := by
    unfold weightedPrimeIntervalSum
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hupper : p ≤ ⌊(25 : ℝ) * R⌋₊ :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    have hreal : (p : ℝ) ≤ 25 * R :=
      (Nat.le_floor_iff (by positivity : 0 ≤ (25 : ℝ) * R)).mp hupper
    rw [oddPrimeLoss_of_le_25 _ ((div_le_iff₀ hR).mpr hreal)]
  rw [hconstant, weightedPrimeIntervalSum_const]
  simp only [primeIntervalSum, Chebyshev.theta, zero_mul, Nat.floor_zero]

theorem oddPrimeLoss_weighted_tendsto_real :
    Tendsto (weightedPrimeIntervalSum oddPrimeLoss 0 65)
      atTop (𝓝 (8609 / 2 : ℝ)) := by
  have hfirst := (theta_scaled_tendsto theta_ratio_tendsto_one
    (by norm_num : (0 : ℝ) < 25)).const_mul (96 : ℝ)
  have hlast := continuous_weightedPrime_tendsto
    (by norm_num : (0 : ℝ) < 25) (by norm_num : (25 : ℝ) < 65)
    (continuous_oddPrimeLoss.continuousOn : ContinuousOn oddPrimeLoss (Set.Icc 25 65))
    theta_ratio_tendsto_one
  rw [integral_oddPrimeLoss_25_65] at hlast
  have hcombined := hfirst.add hlast
  norm_num at hcombined
  apply hcombined.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simpa only [oddPrimeLoss_weighted_0_25 R hR] using
    (weightedPrimeIntervalSum_add_adjacent oddPrimeLoss
      (by norm_num : (0 : ℝ) ≤ 25) (by norm_num : (25 : ℝ) ≤ 65) hR.le)

theorem oddPrimeLoss_prime_sum_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ Finset.Ioc 0 (65 * N) with p.Prime,
        oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / N)
      atTop (𝓝 (8609 / 2 : ℝ)) := by
  have h := oddPrimeLoss_weighted_tendsto_real.comp tendsto_natCast_atTop_atTop
  have hfloor (N : ℕ) : ⌊(65 : ℝ) * N⌋₊ = 65 * N := by
    rw [show (65 : ℝ) * N = ((65 * N : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
    exact Nat.floor_natCast _
  simpa only [Function.comp_def, weightedPrimeIntervalSum, zero_mul,
    Nat.floor_zero, hfloor] using h

end InternalCatalan

end

section

open Filter
open scoped Topology BigOperators
open Zeta5.Workers.W14

namespace InternalCatalan

noncomputable def removedPrimeLoss (N : ℕ) : ℝ :=
  (∑ p ∈ (Finset.Ioc 0 (H N)).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ 2 * Real.sqrt (H N)),
    oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / N

theorem removedPrimeLoss_nonneg (N : ℕ) : 0 ≤ removedPrimeLoss N := by
  unfold removedPrimeLoss
  apply div_nonneg _ (Nat.cast_nonneg N)
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (oddPrimeLoss_mem_Icc _).1
    (log_prime_nonneg (Finset.mem_filter.mp hp).2.1)

theorem removedPrimeLoss_le (N : ℕ) :
    removedPrimeLoss N ≤
      (96 * Real.log 4 * 2) * (Real.sqrt (H N) / N) := by
  let y : ℝ := 2 * Real.sqrt (H N)
  let s := (Finset.Ioc 0 (H N)).filter
    (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ y)
  let t := (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hsub : s ⊆ t := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, hprime, hcut⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hpI).1,
        (Nat.le_floor_iff hy).mpr hcut⟩, hprime⟩
  have hsum : (∑ p ∈ s, oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) ≤
      96 * Chebyshev.theta y := by
    calc
      _ ≤ ∑ p ∈ s, (96 : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (oddPrimeLoss_mem_Icc _).2
          (log_prime_nonneg (Finset.mem_filter.mp hp).2.1)
      _ ≤ ∑ p ∈ t, (96 : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        exact mul_nonneg (by norm_num)
          (log_prime_nonneg (Finset.mem_filter.mp hp).2)
      _ = 96 * Chebyshev.theta y := by
        simp only [t, Chebyshev.theta, Finset.mul_sum]
  calc
    removedPrimeLoss N ≤ (96 * Chebyshev.theta y) / N :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
    _ ≤ (96 * (Real.log 4 * y)) / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hy) (by norm_num))
        (Nat.cast_nonneg N)
    _ = (96 * Real.log 4 * 2) * (Real.sqrt (H N) / N) := by
      dsimp [y]
      ring

theorem sqrt_H_div_tendsto_zero :
    Tendsto (fun N : ℕ => Real.sqrt (H N) / N) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp hcast)).const_mul (Real.sqrt 65)
  simpa only [H, Nat.cast_mul, Nat.cast_ofNat, Function.comp_def,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 65),
    mul_div_assoc, Real.sqrt_div_self, mul_zero] using h

theorem removedPrimeLoss_tendsto_zero :
    Tendsto removedPrimeLoss atTop (𝓝 0) := by
  have h := sqrt_H_div_tendsto_zero.const_mul (96 * Real.log 4 * 2)
  simp only [mul_zero] at h
  exact squeeze_zero removedPrimeLoss_nonneg removedPrimeLoss_le h

theorem oddPrimeLoss_large_prime_sum_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter
          (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / N)
      atTop (𝓝 (8609 / 2 : ℝ)) := by
  have h := oddPrimeLoss_prime_sum_tendsto.sub removedPrimeLoss_tendsto_zero
  simp only [sub_zero] at h
  apply h.congr
  intro N
  apply (sub_eq_iff_eq_add).mpr
  unfold removedPrimeLoss
  rw [← add_div]
  congr 1
  change (∑ p ∈ Finset.Ioc 0 (H N) with p.Prime,
      oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) = _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : p.Prime
  · by_cases hcut : (p : ℝ) ≤ 2 * Real.sqrt (H N)
    · simp [hprime, hcut, not_lt.mpr hcut]
    · simp [hprime, hcut, lt_of_not_ge hcut]
  · simp [hprime]

theorem large_prime_cutoff_ne_two {N p : ℕ} (hN : 0 < N)
    (hp : 2 * Real.sqrt (H N) < (p : ℝ)) : p ≠ 2 := by
  have hH : (1 : ℝ) ≤ (H N : ℝ) := by
    exact_mod_cast (show 1 ≤ H N by unfold H; omega)
  have hs := Real.one_le_sqrt.mpr hH
  intro heq
  subst p
  norm_num only [Nat.cast_ofNat] at hp
  linarith

end InternalCatalan

end


namespace InternalCatalan

open Filter

theorem large_prime_cutoff_square {N p : ℕ}
    (hp : 2 * Real.sqrt (H N) < (p : ℝ)) : 4 * H N < p ^ 2 := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (H N))
  have hs := Real.sqrt_nonneg (H N)
  have hr : (4 : ℝ) * (H N : ℝ) < (p : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (p : ℝ) by positivity]
  exact_mod_cast hr

theorem large_prime_cutoff_gt_fixed {B N p : ℕ} (hB : B ^ 2 ≤ N)
    (hp : 2 * Real.sqrt (H N) < (p : ℝ)) : B < p := by
  have hBH : B ^ 2 ≤ H N := by unfold H; omega
  have hs : (B : ℝ) ≤ Real.sqrt (H N) :=
    (Real.le_sqrt (Nat.cast_nonneg B) (Nat.cast_nonneg (H N))).mpr
      (by exact_mod_cast hBH)
  have hreal : (B : ℝ) < (p : ℝ) := by
    linarith [Real.sqrt_nonneg (H N)]
  exact_mod_cast hreal

theorem large_prime_witness_den_eventually (z : ℚ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      2 * Real.sqrt (H N) < (p : ℝ) → (z.den : ZMod p) ≠ 0 := by
  filter_upwards [eventually_ge_atTop (z.den ^ 2)] with N hN
  intro p hp hz
  have hden := large_prime_cutoff_gt_fixed hN hp
  exact (Nat.not_dvd_of_pos_of_lt z.pos hden)
    ((ZMod.natCast_eq_zero_iff z.den p).mp hz)

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology BigOperators

theorem oddPrimeLoss_large_prime_normalized_tendsto :
    Tendsto (fun N : ℕ =>
      (N : ℝ) *
        (∑ p ∈ (Finset.Ioc 0 (H N)).filter
            (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
          oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / (n N : ℝ) ^ 2)
      atTop (𝓝 (8609 / 4608 : ℝ)) := by
  have hs := oddPrimeLoss_large_prime_sum_tendsto.div_const (2304 : ℝ)
  norm_num only [div_div, show (2 : ℝ) * 2304 = 4608 by norm_num] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [n, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNr]
  ring

theorem oddPrimeLoss_large_prime_normalized_eventually_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) *
        (∑ p ∈ (Finset.Ioc 0 (H N)).filter
            (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
          oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ)) / (n N : ℝ) ^ 2 <
        (8609 / 4608 : ℝ) + ε :=
  (tendsto_order.mp oddPrimeLoss_large_prime_normalized_tendsto).2 _ (by linarith)

end InternalCatalan

end

end OAI
