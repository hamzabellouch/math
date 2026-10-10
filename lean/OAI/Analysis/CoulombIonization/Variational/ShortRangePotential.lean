import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombBallIntegral

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped ENNReal

namespace CoulombAnalysis

lemma coulomb_short_range_holder {R : ℝ} (hR : 0 < R)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (ballMeasure R)) :
    (∫ x in ball 0 R, ‖f x‖/‖x‖) ≤
      (∫ x in ball 0 R, ‖f x‖^(5/3:ℝ))^(3/5:ℝ) *
      (8*Real.pi)^(2/5:ℝ) * R^(1/5:ℝ) := by
  have hf' : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (5/3:ℝ)) (ballMeasure R) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3),ENNReal.ofReal_ofNat] using hf.norm
  have hk : MemLp (fun x : TFSpace => ‖x‖⁻¹) (ENNReal.ofReal (5/2:ℝ)) (ballMeasure R) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2),ENNReal.ofReal_ofNat] using nuclear_memLp R
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (5/3:ℝ).HolderConjugate (5/2) from Real.holderConjugate_iff.mpr (by norm_num))
    (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
    (Filter.Eventually.of_forall fun x : TFSpace => inv_nonneg.mpr (norm_nonneg x)) hf' hk
  have he : (∫ x, (‖x‖⁻¹)^(5/2:ℝ) ∂ballMeasure R) = 8*Real.pi*R^(1/2:ℝ) := by
    simpa only [ballMeasure,←Real.rpow_neg_eq_inv_rpow,neg_div] using integral_coulomb_power_ball hR
  rw [he] at hh
  norm_num only [one_div_div,mul_one] at hh
  have he' : (8*Real.pi*R^(1/2:ℝ))^(2/5:ℝ) =
      (8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hR.le]
    norm_num
  rw [he'] at hh
  simpa only [ballMeasure,div_eq_mul_inv,mul_assoc] using hh

lemma coulomb_short_range_bounded {R C : ℝ} (hR : 0 < R)
    {f : TFSpace → ℝ} (hf : AEStronglyMeasurable f (ballMeasure R))
    (hbound : ∀ᵐ x ∂ballMeasure R, ‖f x‖ ≤ C) :
    (∫ x in ball 0 R, ‖f x‖/‖x‖) ≤ C*(2*Real.pi*R^2) := by
  have hk := (nuclear_memLp R).integrable (Fact.out : (1:ENNReal) ≤ 5/2)
  have hi : Integrable (fun x : TFSpace => ‖f x‖/‖x‖) (ballMeasure R) := by
    apply (hk.const_mul C).mono'
      (by convert! hf.norm.mul hk.aestronglyMeasurable using 1)
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact (div_le_div_of_nonneg_right hx (norm_nonneg x)).trans_eq (div_eq_mul_inv _ _)
  have hh := integral_mono_ae hi (hk.const_mul C) (hbound.mono fun x hx => by
    change ‖f x‖/‖x‖ ≤ C*‖x‖⁻¹
    rw [←div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hx (norm_nonneg x))
  simpa only [ballMeasure,integral_const_mul,integral_coulomb_ball hR] using hh

end CoulombAnalysis

end

end OAI
