import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant
import OAI.NumberTheory.Catalan.Estimates.MixedMajorant
import OAI.NumberTheory.Catalan.Estimates.ScalarMomentDecay

namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set Real Polynomial

private theorem intervalIntegrable_one_sub_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(3 / 4) : ℝ)) volume 0 1 := by
  have h := intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := 1) (r := -(3 / 4)) (by norm_num)
  simpa only [sub_zero, sub_self] using (h.comp_sub_left 1).symm

private theorem intervalIntegrable_one_sub_abs_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ)) volume (-1) 1 := by
  have hp : IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ))
      volume 0 1 := by
    apply intervalIntegrable_one_sub_rpow.congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [abs_of_pos ht.1]
  have hn : IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ))
      volume (-1) 0 := by
    simpa only [zero_sub, sub_zero, abs_neg] using (hp.comp_sub_left 0).symm
  exact hn.trans hp

theorem integrable_mixedMajorant :
    Integrable (fun p : ℝ × ℝ =>
      (1 - |p.1|) ^ (-(3 / 4) : ℝ) * (1 - p.2) ^ (-(3 / 4) : ℝ))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have ht := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mp intervalIntegrable_one_sub_abs_rpow
  have hs := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp intervalIntegrable_one_sub_rpow
  exact ht.mul_prod hs

theorem ae_mem_mixed_rectangle :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)),
      p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact ⟨ht, hs⟩

theorem integrable_mixedKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)) := by
    fun_prop
  apply integrable_mixedMajorant.mono' hm.aestronglyMeasurable
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  exact norm_mixedKernel_le i j hp.1 hp.2

theorem mixedMoment_X_pow_eq_integral_prod (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) =
      ∫ p : ℝ × ℝ,
        (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h := integral_prod
    (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2))
    (integrable_mixedKernel i j)
  simpa only [mixedMoment, Polynomial.eval_pow, Polynomial.eval_X,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

theorem integral_prod_mixedMonomial (i j : ℕ) :
    (∫ p : ℝ × ℝ, (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      (momentScalar i : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  have ht : (∫ t in Ioo (-1 : ℝ) 1, t ^ i * (|t| / sqrt (1 - t ^ 2))) =
      scalarMoment i := by
    simp only [scalarMoment, intervalIntegral.integral_of_le
      (show (-1 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]
  have hs : (∫ s in Ioo (0 : ℝ) 1, s ^ j) = 1 / ((j + 1 : ℕ) : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), integral_pow]
    simp only [one_pow, zero_pow (Nat.add_one_ne_zero _), sub_zero, Nat.cast_add,
      Nat.cast_one]
  calc
    _ = ∫ p : ℝ × ℝ, (p.1 ^ i * (|p.1| / sqrt (1 - p.1 ^ 2))) * p.2 ^ j
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = (scalarMoment i) * (1 / ((j + 1 : ℕ) : ℝ)) := by
      rw [integral_prod_mul (fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
        (fun s : ℝ => s ^ j), ht, hs]
    _ = _ := by rw [scalarMoment_eq_momentScalar]; ring

theorem mixedMoment_X_pow_step (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) - mixedMoment (X ^ (i + 1)) (X ^ (j + 1)) =
      (momentScalar i : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  rw [mixedMoment_X_pow_eq_integral_prod, mixedMoment_X_pow_eq_integral_prod,
    ← integral_sub (integrable_mixedKernel i j) (integrable_mixedKernel (i + 1) (j + 1))]
  rw [← integral_prod_mixedMonomial i j]
  apply integral_congr_ae
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  have habs : |p.1| < 1 := abs_lt.mpr hp.1
  have ht : p.1 * p.2 < 1 := by
    have hle : p.1 * p.2 ≤ |p.1| * p.2 := mul_le_mul_of_nonneg_right (le_abs_self _) hp.2.1.le
    have hlt : |p.1| * p.2 < 1 := by nlinarith [abs_nonneg p.1, habs, hp.2.1, hp.2.2]
    exact hle.trans_lt hlt
  have hd : 1 - p.1 * p.2 ≠ 0 := by linarith
  simp only [pow_succ]
  rw [← sub_div]
  apply (div_eq_iff hd).mpr
  ring

open MeasureTheory Set Real Polynomial
open scoped BigOperators Topology

theorem hasSum_mixedKernel (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun u : ℕ =>
      (|t| / sqrt (1 - t ^ 2)) * (t ^ (i + u) * s ^ (j + u)))
      ((|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) := by
  have ha : |t| < 1 := abs_lt.mpr ht
  have hts : |t * s| < 1 := by
    rw [abs_mul, abs_of_pos hs.1]
    have hle : |t| * s ≤ |t| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2.le (abs_nonneg t)
    exact hle.trans_lt ha
  convert (hasSum_geometric_of_abs_lt_one hts).mul_left
    ((|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j)) using 1
  · ext u
    simp only [pow_add, mul_pow]
    ring
  · rfl

theorem integrable_abs_mixedKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ i * p.2 ^ j) / (1 - |p.1| * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ i * p.2 ^ j) / (1 - |p.1| * p.2)) := by
    fun_prop
  apply integrable_mixedMajorant.mono' hm.aestronglyMeasurable
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  have ht : |p.1| ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [abs_nonneg p.1], abs_lt.mpr hp.1⟩
  simpa only [abs_abs, sq_abs] using norm_mixedKernel_le i j ht hp.2

theorem hasSum_mixedMoment_X_pow (i j : ℕ) :
    HasSum (fun u : ℕ =>
      (momentScalar (i + u) : ℝ) / ((j + u + 1 : ℕ) : ℝ))
      (mixedMoment (X ^ i) (X ^ j)) := by
  let μ := (volume.restrict (Ioo (-1 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1))
  let F : ℕ → ℝ × ℝ → ℝ := fun u p =>
    (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ (i + u) * p.2 ^ (j + u))
  let B : ℕ → ℝ × ℝ → ℝ := fun u p =>
    (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ (i + u) * p.2 ^ (j + u))
  let G : ℝ × ℝ → ℝ := fun p =>
    (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ i * p.2 ^ j) / (1 - |p.1| * p.2)
  have hsumB : ∀ᵐ p ∂μ, HasSum (fun u => B u p) (G p) := by
    filter_upwards [ae_mem_mixed_rectangle] with p hp
    have ht : |p.1| ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [abs_nonneg p.1], abs_lt.mpr hp.1⟩
    simpa only [B, G, abs_abs, sq_abs] using hasSum_mixedKernel i j ht hp.2
  have hsum_int : Integrable (fun p => ∑' u, B u p) μ := by
    apply (integrable_abs_mixedKernel i j).congr
    filter_upwards [hsumB] with p hp
    exact hp.tsum_eq.symm
  have hbound : ∀ u, ∀ᵐ p ∂μ, ‖F u p‖ ≤ B u p := by
    intro u
    filter_upwards [ae_mem_mixed_rectangle] with p hp
    have hw : 0 ≤ |p.1| / sqrt (1 - p.1 ^ 2) :=
      div_nonneg (abs_nonneg _) (sqrt_nonneg _)
    simp only [F, B, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw,
      abs_pow, abs_of_pos hp.2.1, le_refl]
  have hlim : ∀ᵐ p ∂μ, HasSum (fun u => F u p)
      ((|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)) := by
    filter_upwards [ae_mem_mixed_rectangle] with p hp
    exact hasSum_mixedKernel i j hp.1 hp.2
  have hmeas (u : ℕ) : AEStronglyMeasurable (F u) μ := by
    have hm : Measurable (F u) := by dsimp only [F]; fun_prop
    exact hm.aestronglyMeasurable
  have h := hasSum_integral_of_dominated_convergence B
    hmeas hbound
    (hsumB.mono fun _ hp => hp.summable) hsum_int hlim
  have hterm (u : ℕ) : (∫ p, F u p ∂μ) =
      (momentScalar (i + u) : ℝ) / ((j + u + 1 : ℕ) : ℝ) :=
    integral_prod_mixedMonomial (i + u) (j + u)
  simp only [hterm] at h
  rw [mixedMoment_X_pow_eq_integral_prod]
  exact h

end InternalCatalan

end

end OAI
