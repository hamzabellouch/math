import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.TemperedHeightWeights

namespace OAI

/-!
# Tempered distributions associated with heights

Polynomially weighted integrability makes the positive and negative height
measures temperate. Their difference defines a tempered distribution whose action
on a Schwartz test function is integration against the signed height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal

def positiveHeightMeasure {d : ℕ} (μ : Measure (Ambient d)) (f : Ambient d → ℝ) :
    Measure (Ambient d) := μ.withDensity (fun x => (Real.toNNReal (f x) : ℝ≥0∞))

theorem positive_height_measure_temperate {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ) :
    (positiveHeightMeasure μ f).HasTemperateGrowth := by
  have hg : Measurable (fun x => Real.toNNReal (f x)) := hf.real_toNNReal
  have hi : Integrable (fun x => (Real.toNNReal (f x) : ℝ) * polynomialDecay q x) μ := by
    apply hweight.mono'
      (((NNReal.continuous_coe.measurable.comp hg).mul (polynomialDecay_measurable q)).aestronglyMeasurable)
    apply Eventually.of_forall
    intro x
    change ‖(Real.toNNReal (f x) : ℝ) * polynomialDecay q x‖ ≤ |f x| * polynomialDecay q x
    rw [Real.norm_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (polynomialDecay_nonneg q x))]
    exact mul_le_mul_of_nonneg_right (Real.coe_toNNReal_le _) (polynomialDecay_nonneg q x)
  refine ⟨⟨q, ?_⟩⟩
  change Integrable (fun x => (1 + ‖x‖) ^ (-(q : ℝ)))
    (μ.withDensity (fun x => (Real.toNNReal (f x) : ℝ≥0∞)))
  apply (integrable_withDensity_iff_integrable_coe_smul hg).mpr
  simpa only [smul_eq_mul, ← polynomialDecay_eq_rpow] using! hi

theorem positivePart_sub_negativePart (r : ℝ) :
    (Real.toNNReal r : ℝ) - (Real.toNNReal (-r) : ℝ) = r := by
  rw [Real.coe_toNNReal', Real.coe_toNNReal']
  rcases le_total 0 r with hr | hr
  · rw [max_eq_left hr, max_eq_right (by linarith : -r ≤ 0), sub_zero]
  · rw [max_eq_right hr, max_eq_left (by linarith : 0 ≤ -r)]
    ring

theorem height_schwartz_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ)
    (g : 𝓢(Ambient d, ℂ)) : Integrable (fun x => f x • g x) μ := by
  let := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  let := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  have hip : Integrable (fun x => (Real.toNNReal (f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ f))
  have hin : Integrable (fun x => (Real.toNNReal (-f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.neg.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ (fun x => -f x)))
  convert! hip.sub hin using 1
  ext x
  change f x • g x = (Real.toNNReal (f x) : ℝ) • g x -
    (Real.toNNReal (-f x) : ℝ) • g x
  calc
    _ = ((Real.toNNReal (f x) : ℝ) - (Real.toNNReal (-f x) : ℝ)) • g x :=
      congrArg (fun r : ℝ => r • g x) (positivePart_sub_negativePart (f x)).symm
    _ = _ := sub_smul (Real.toNNReal (f x) : ℝ) (Real.toNNReal (-f x) : ℝ) (g x)

def heightTemperedDistribution {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ) : 𝓢'(Ambient d, ℂ) := by
  letI := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  letI := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  exact (positiveHeightMeasure μ f).toTemperedDistribution -
    (positiveHeightMeasure μ (fun x => -f x)).toTemperedDistribution

theorem heightTemperedDistribution_apply {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ)
    (g : 𝓢(Ambient d, ℂ)) : heightTemperedDistribution μ f hf q hweight g = ∫ x, f x • g x ∂μ := by
  let := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  let := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  have hip : Integrable (fun x => (Real.toNNReal (f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ f))
  have hin : Integrable (fun x => (Real.toNNReal (-f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.neg.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ (fun x => -f x)))
  change (∫ x, g x ∂positiveHeightMeasure μ f) -
    (∫ x, g x ∂positiveHeightMeasure μ (fun x => -f x)) = ∫ x, f x • g x ∂μ
  unfold positiveHeightMeasure
  rw [integral_withDensity_eq_integral_smul hf.real_toNNReal,
    integral_withDensity_eq_integral_smul (show Measurable (fun x => Real.toNNReal (-f x)) from hf.neg.real_toNNReal)]
  simp only [NNReal.smul_def]
  refine (integral_sub hip hin).symm.trans (integral_congr_ae (Eventually.of_forall ?_))
  intro x
  calc
    _ = ((Real.toNNReal (f x) : ℝ) - (Real.toNNReal (-f x) : ℝ)) • g x :=
      (sub_smul (Real.toNNReal (f x) : ℝ) (Real.toNNReal (-f x) : ℝ) (g x)).symm
    _ = _ := congrArg (fun r : ℝ => r • g x) (positivePart_sub_negativePart (f x))

theorem heightTemperedDistribution_independent_of_weight {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (p q : ℕ)
    (hp : Integrable (fun x => |f x| * polynomialDecay p x) μ)
    (hq : Integrable (fun x => |f x| * polynomialDecay q x) μ) :
    heightTemperedDistribution μ f hf p hp = heightTemperedDistribution μ f hf q hq := by
  ext g
  rw [heightTemperedDistribution_apply, heightTemperedDistribution_apply]

end

end RieszRectifiability

end OAI
