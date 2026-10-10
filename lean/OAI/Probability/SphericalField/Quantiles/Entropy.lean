import Mathlib
import OAI.Probability.SphericalField.Quantiles.Distribution

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

theorem entropy_quantileTrial (q : Time → Time) (hq : Measurable q)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1) (hqb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    entropy (quantileTrial q)=ENNReal.ofReal
      (((∫ t in (0:ℝ)..B, (quantileTail q t)⁻¹)+Real.log (1-B))/2) := by
  let D := quantileTail q
  let F : ℝ → ℝ := fun t => (D t)⁻¹-(1-t)⁻¹
  have hD (t : ℝ) (ht : t ≤ B) : 0 < D t := (sub_pos.mpr hB1).trans_le (quantileTail_lower q hq hqb ht)
  have hF : ContinuousOn F (Icc 0 B) :=
    ((quantileTail_lipschitz q hq).continuous.continuousOn.inv₀ (fun t ht => (hD t ht.2).ne')).sub
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t ht => by
        have : t < 1 := ht.2.trans_lt hB1
        exact (sub_pos.mpr this).ne'))
  have hF0 : ∀ t ∈ Icc 0 B, 0 ≤ F t := by
    intro t ht
    exact sub_nonneg.mpr (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1)) (hD t ht.2) |>.mpr
      (quantileTail_upper q hq t))
  have he (t : Time) : (ENNReal.ofReal (tailIntegral (quantileTrial q) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ = (Iic B).indicator (fun t => ENNReal.ofReal (F t)) (t:ℝ) := by
    rw [tailIntegral_quantileTrial q hq]
    change (ENNReal.ofReal (D (t:ℝ)))⁻¹-_ = _
    by_cases ht : (t:ℝ) ≤ B
    · rw [Set.indicator_of_mem (show (t:ℝ) ∈ Iic B from ht)]
      dsimp [F]
      rw [ENNReal.ofReal_sub _ (inv_nonneg.mpr (sub_nonneg.mpr t.2.2)),
        ENNReal.ofReal_inv_of_pos (hD t ht),
        ENNReal.ofReal_inv_of_pos (sub_pos.mpr (ht.trans_lt hB1))]
    · rw [Set.indicator_of_notMem (show (t:ℝ) ∉ Iic B from ht)]
      have hd : D (t:ℝ) = 1-(t:ℝ) := quantileTail_of_le q (hqb.mono (fun u hu => hu.trans (le_of_not_ge ht)))
      rw [hd,tsub_self]
  have hset : Iic B ∩ Icc (0:ℝ) 1 = Icc 0 B := by
    ext t
    constructor
    · rintro ⟨ht,h0,h1⟩
      exact ⟨h0,ht⟩
    · rintro ⟨h0,ht⟩
      exact ⟨ht,h0,ht.trans hB1.le⟩
  have hel : (∫⁻ t : Time, (ENNReal.ofReal (tailIntegral (quantileTrial q) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ ∂timeLaw) = ENNReal.ofReal (∫ t in Icc 0 B, F t) := by
    rw [lintegral_congr he]
    change (∫⁻ t : Icc (0:ℝ) 1, (Iic B).indicator (fun t => ENNReal.ofReal (F t)) t.val
      ∂Measure.comap Subtype.val volume) = _
    rw [lintegral_subtype_comap measurableSet_Icc,lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic,hset]
    exact (ofReal_integral_eq_lintegral_ofReal hF.integrableOn_Icc
      ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hF0 t ht))).symm
  have hInt : (∫ t in Icc 0 B, F t) = (∫ t in (0:ℝ)..B, (D t)⁻¹)+Real.log (1-B) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hB0]
    have hiD : IntervalIntegrable (fun t => (D t)⁻¹) volume 0 B :=
      ((quantileTail_lipschitz q hq).continuous.continuousOn.inv₀ (fun t ht => (hD t ht.2).ne')).intervalIntegrable_of_Icc hB0
    have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t (ht : t ∈ Icc (0:ℝ) B) =>
        (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
    rw [show F = (fun t => (D t)⁻¹-(1-t)⁻¹) from rfl,
      intervalIntegral.integral_sub hiD hiR,integral_one_sub_inv hB1,sub_neg_eq_add]
  rw [entropy,hel,hInt,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num
  rfl

end SphericalPerceptron
end
end

end OAI
