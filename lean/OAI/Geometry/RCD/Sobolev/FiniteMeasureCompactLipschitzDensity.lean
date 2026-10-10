import OAI.Analysis.RCDHeat.Density
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace OAI

/-! # Compact Lipschitz approximation against a finite dominating measure -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] [IsFiniteMeasure μ]

theorem finite_measure_compact_lipschitz_L1 {f : X → ℝ} (hf : MemLp f 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : X → ℝ) (L : ℝ≥0), LipschitzWith L g ∧ HasCompactSupport g ∧
      Integrable g μ ∧ (∫ x, |f x-g x| ∂μ) < ε := by
  let B := μ univ ^ (1/2 : ℝ)
  have hB : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ univ)
  let δ := ε/(B.toReal+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g,hg,⟨L,hL⟩,hgm,hgc⟩ := MemLp.exists_lipschitz_hasCompactSupport_eLpNorm_sub_le μ hf
    (ε := ENNReal.ofReal δ) (by positivity)
  have ha := (hf.sub hgm).aestronglyMeasurable
  have hone : eLpNorm (f-g) 1 μ ≤ ENNReal.ofReal δ*B := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1:ℝ≥0∞) ≤ 2) ha
    have he : (1/(1:ℝ≥0∞).toReal-1/(2:ℝ≥0∞).toReal : ℝ) = 1/2 := by norm_num
    rw [he] at h
    exact h.trans (by gcongr)
  refine ⟨g,L,hL,hgc,(hgm.mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2)).integrable (by norm_num),?_⟩
  have hnorm : (∫ x, |f x-g x| ∂μ) = (eLpNorm (f-g) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm ha]
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using integral_norm_eq_lintegral_enorm ha
  rw [hnorm]
  have hsmall : δ*B.toReal < ε := by
    have he : (B.toReal+1)*δ = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith [ENNReal.toReal_nonneg (a := B)]
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) hone).trans_lt
    (by simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hδ.le] using hsmall)

end RegularPointCoordinates

end

end OAI
