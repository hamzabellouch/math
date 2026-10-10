import OAI.NumberTheory.CubicMoment.Estimates.LowHeightIntegral
import OAI.NumberTheory.CubicMoment.Estimates.SharpHeightMultiplier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The sharp height multiplier has logarithmic integral cost. This is
needed when only a fixed power of logarithmic saving is available. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma lowHeightWeight_norm_le_decay (H T t : ℝ) :
    ‖lowHeightWeight H T t‖ ≤ 4/(1+|t|) := by
  have hd : 0 < 1+|t| := by positivity
  by_cases ht : |t| ≤ 1
  · apply (lowHeightWeight_norm_le H T t).trans
    have hl : Real.log 2 ≤ 1 := by
      simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    exact hl.trans ((le_div_iff₀ hd).mpr (by linarith [abs_nonneg t]))
  · have hp : 0 < |t| := by linarith
    have hb : ‖lowHeightWeight H T t‖ ≤ 2/|t| := by
      rw [lowHeightWeight,norm_mul]
      apply (mul_le_of_le_one_right (_root_.norm_nonneg _) ?_).trans
        (cutoffHeightMultiplier_norm_le H (abs_pos.mp hp))
      simpa only [Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg heightPartitionBump.nonneg] using
        (heightPartitionBump.le_one (x := t/T))
    apply hb.trans
    apply (div_le_div_iff₀ hp hd).mpr
    linarith

lemma integral_reciprocal_one_add_abs {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in -R..R, (1+|t|)⁻¹) = 2*Real.log (1+R) := by
  let f := fun t : ℝ => (1+|t|)⁻¹
  have hf : Continuous f := by
    exact (continuous_const.add continuous_abs).inv₀ (show ∀ t : ℝ, 1+|t| ≠ 0 from fun t => (by positivity : (0:ℝ) < 1+|t|).ne')
  have hi : (∫ t in 0..R, f t) = Real.log (1+R) := by
    calc
      _ = ∫ t in 0..R, (t+1)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hR] at ht
        simp only [f,abs_of_nonneg ht.1,add_comm]
      _ = ∫ t in 1..R+1, t⁻¹ := by
        simpa only [zero_add] using
          (intervalIntegral.integral_comp_add_right (fun t : ℝ => t⁻¹) 1 (a := 0) (b := R))
      _ = Real.log (1+R) := by
        rw [integral_inv_of_pos zero_lt_one (by linarith)]
        simp only [div_one,add_comm]
  have hn : (∫ t in -R..0, f t) = ∫ t in 0..R, f t := by
    have he := intervalIntegral.integral_comp_neg f (a := 0) (b := R)
    simpa only [neg_zero,abs_neg,f] using he.symm
  change (∫ t in -R..R, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-R) 0) (hf.intervalIntegrable 0 R),hn,hi]
  ring

theorem lowHeightWeight_integral_log_bound (H : ℝ) {T B : ℝ}
    (hT : 0 < T) (_hB : 0 ≤ B) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Icc (-(4/3)*T) ((4/3)*T), ‖f t‖ ≤ B) :
    ‖∫ t : ℝ, lowHeightWeight H T t*f t‖ ≤ 8*B*Real.log (1+(4/3)*T) := by
  let R : ℝ := (4/3)*T
  let S : Set ℝ := Icc (-R) R
  let g := fun t : ℝ => 4*B*(1+|t|)⁻¹
  have hg : Continuous g := by
    apply continuous_const.mul
    exact (continuous_const.add continuous_abs).inv₀ (show ∀ t : ℝ, 1+|t| ≠ 0 from fun t => (by positivity : (0:ℝ) < 1+|t|).ne')
  have hi : Integrable (S.indicator g) :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hb : ‖∫ t : ℝ, lowHeightWeight H T t*f t‖ ≤ ∫ t : ℝ, S.indicator g t := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht,norm_mul]
      calc
        _ ≤ (4/(1+|t|))*B := mul_le_mul (lowHeightWeight_norm_le_decay H T t)
          (hf t (by simpa only [S,R,neg_mul] using ht)) (_root_.norm_nonneg _) (by positivity)
        _ = g t := by dsimp [g]; ring
    · rw [indicator_of_notMem ht,lowHeightWeight_zero H hT (by
        simpa only [S,R,neg_mul] using ht),zero_mul,norm_zero]
  apply hb.trans_eq
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by dsimp [R]; linarith)]
  change (∫ t in -R..R, 4*B*(1+|t|)⁻¹) = _
  rw [intervalIntegral.integral_const_mul,integral_reciprocal_one_add_abs (by dsimp [R]; positivity)]
  dsimp [R]
  ring

end CubicFirstMoment

end

end OAI
