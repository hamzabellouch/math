import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePhase
import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Uniform prime-phase repulsion for the moderate-frequency part of MRT
Appendix A. The fourth-root logarithmic coordinate keeps the exponentially
small PNT error separate from the polynomial frequency range. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Topology

lemma halasz_polynomial_phase_error (c K : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, (8 + y ^ 80) * K * Real.exp (-c * y) ≤ 1 := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  have h80 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (80 : ℕ) c hc
  simp only [Real.rpow_natCast] at h80
  have hh := ((h0.const_mul 8).add h80).mul_const K
  have hlim : Tendsto (fun y : ℝ => (8 + y ^ 80) * K * Real.exp (-c * y))
      atTop (𝓝 0) := by
    convert hh using 1
    · ext y
      simp only [Real.rpow_zero, one_mul]
      ring
    · norm_num
  exact (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
    (fun _ h => h.le)

lemma halasz_logarithmic_phase_scale (N : ℕ) (y : ℝ) (hy : 1 < y)
    (hN : Real.log N = y ^ 4) :
    Real.exp 1 ≤ Real.exp (y ^ 2) ∧ Real.exp (y ^ 2) ≤ N ∧
      Real.log (Real.log N / Real.log (Real.exp (y ^ 2))) =
        Real.log (Real.log N) / 2 := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hy2 : 1 < y ^ 2 := by nlinarith
  have hNp : 0 < (N : ℝ) := by
    have hh : 1 < (N : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg N)).mp
      (by rw [hN]; positivity)
    linarith
  refine ⟨Real.exp_le_exp.mpr hy2.le, ?_, ?_⟩
  · rw [← Real.exp_log hNp, hN]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (y ^ 2 - 1)]
  · rw [Real.log_exp, hN, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    ring

/-- Uniform masked distance repulsion in the moderate frequency range.
The lower bound is independent of the deleted prime set. -/
theorem halasz_moderate_masked_distance :
    ∀ᶠ y : ℝ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (N : ℕ) (t t₁ : ℝ), Real.log N = y ^ 4 →
      1 ≤ |t - t₁| * y ^ 2 → |t - t₁| ≤ y ^ 80 →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      Real.log (Real.log N) / 16 - 1 / 2 ≤
        squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  obtain ⟨c, K, hc, hK, hphase⟩ := modFiveThetaInput.halasz_masked_phase_lower
  filter_upwards [eventually_gt_atTop (1 : ℝ), halasz_polynomial_phase_error c K hc]
    with y hy herr
  intro F hF Q N t t₁ hN htlo hthi hmin
  obtain ⟨hlo, hhi, hlog⟩ := halasz_logarithmic_phase_scale N y hy hN
  have hh := hphase F hF Q N (Real.exp (y ^ 2)) t t₁ hlo hhi
    (by simpa only [Real.log_exp] using htlo) hmin
  rw [hlog, Real.log_exp, Real.sqrt_sq (by linarith : 0 ≤ y)] at hh
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hnum : (8 + |t - t₁|) * K * Real.exp (-c * y) ≤ 1 := by
    apply le_trans _ herr
    gcongr
  have herr' : (8 + |t - t₁|) * K * Real.exp (-c * y) / y ^ 2 ≤ 1 := by
    exact (div_le_one (by positivity : 0 < y ^ 2)).mpr (hnum.trans hy2)
  linarith

/-- The moderate-frequency clause in the original natural cutoff, with a
fixed positive margin over the exponent needed in the last MRT class. -/
theorem halasz_moderate_distance_nat :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (t t₁ : ℝ),
      (Real.log N) ^ (1 / (16 : ℝ)) / 2 ≤ |t - t₁| →
      |t - t₁| ≤ (Real.log N) ^ 20 →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      (31 / 500 : ℝ) * Real.log (Real.log N) ≤
        squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (Real.log N)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hlog)
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (1000 : ℝ))
  filter_upwards [hroot.eventually halasz_moderate_masked_distance,
    hlog.eventually (eventually_ge_atTop (4 : ℝ)), hll] with N hN hl hllN
  dsimp only [Function.comp_def] at hllN
  intro F hF Q t t₁ htlo hthi hmin
  have hl0 : 0 ≤ Real.log N := by linarith
  have hs : Real.sqrt (Real.sqrt (Real.log N)) ^ 2 = Real.sqrt (Real.log N) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hfour : Real.sqrt (Real.sqrt (Real.log N)) ^ 4 = Real.log N := by
    calc
      _ = (Real.sqrt (Real.sqrt (Real.log N)) ^ 2) ^ 2 := by ring
      _ = Real.log N := by rw [hs, Real.sq_sqrt hl0]
  have h80 : Real.sqrt (Real.sqrt (Real.log N)) ^ 80 = (Real.log N) ^ 20 := by
    calc
      _ = (Real.sqrt (Real.sqrt (Real.log N)) ^ 4) ^ 20 := by rw [← pow_mul]
      _ = _ := by rw [hfour]
  have hs2 : 2 ≤ Real.sqrt (Real.log N) := by
    have hsq := Real.sq_sqrt hl0
    have hn := Real.sqrt_nonneg (Real.log N)
    nlinarith
  have hrpow : 1 ≤ (Real.log N) ^ (1 / (16 : ℝ)) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hu : 1 / 2 ≤ |t - t₁| := by linarith
  have ht : 1 ≤ |t - t₁| * Real.sqrt (Real.log N) := by nlinarith
  have hh := hN F hF Q N t t₁ hfour.symm
    (by simpa only [hs] using ht) (by simpa only [h80] using hthi) hmin
  linarith

end TwoPointCorrelations

end OAI
