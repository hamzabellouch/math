import OAI.Probability.DilutedSpin.CompoundMoment

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

lemma compoundPoisson_map_linear [CompleteSpace F] (r : ℝ≥0) (μ : Measure E)
    [IsProbabilityMeasure μ] (A : E →L[ℝ] F) :
    Measure.map A (compoundPoisson r μ) = compoundPoisson r (Measure.map A μ) := by
  let : IsProbabilityMeasure (Measure.map A μ) :=
    (Measure.isProbabilityMeasure_map_iff A.measurable.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map,charFunDual_compoundPoisson,charFunDual_compoundPoisson,charFunDual_map]

omit [NormedSpace ℝ E] [SecondCountableTopology E] in
lemma integrable_lipschitz_of_id (μ : Measure E) [IsFiniteMeasure μ]
    (hi : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) : Integrable f μ := by
  apply ((hi.norm.const_mul (C:ℝ)).add (integrable_const |f 0|)).mono' hf.continuous.measurable.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hh := hf.norm_sub_le x 0
  simp only [Real.norm_eq_abs,sub_zero] at hh
  calc
    |f x| = |(f x-f 0)+f 0| := by rw [sub_add_cancel]
    _ ≤ |f x-f 0|+|f 0| := abs_add_le _ _
    _ ≤ (C:ℝ)*‖x‖+|f 0| := by linarith

lemma integral_norm_sub_compound [CompleteSpace E] (r : ℝ≥0) (μ : Measure (E×E))
    [IsProbabilityMeasure μ] (hi : Integrable id μ) :
    (∫ z, ‖z.1-z.2‖ ∂compoundPoisson r μ) ≤ r*(∫ z,‖z.1-z.2‖ ∂μ) := by
  let A := ContinuousLinearMap.fst ℝ E E-ContinuousLinearMap.snd ℝ E E
  have hm : Measure.map A (compoundPoisson r μ) = compoundPoisson r (Measure.map A μ) :=
    compoundPoisson_map_linear r μ A
  let : IsProbabilityMeasure (Measure.map A μ) :=
    (Measure.isProbabilityMeasure_map_iff A.measurable.aemeasurable).mpr inferInstance
  have hai : Integrable id (Measure.map A μ) :=
    (integrable_map_measure aestronglyMeasurable_id A.measurable.aemeasurable).mpr (A.integrable_comp hi)
  have hb := compoundPoisson_norm_le r (Measure.map A μ) hai
  rw [← hm,integral_map A.measurable.aemeasurable (by fun_prop),
    integral_map A.measurable.aemeasurable (by fun_prop)] at hb
  exact hb

/-- A first-moment transport bound for the physical marked Poisson process.
It also justifies deletion of all repeated-new-site bonds at their actual cost. -/
lemma compoundPoisson_lipschitz_coupling [CompleteSpace E] (r : ℝ≥0) (μ : Measure (E×E))
    [IsProbabilityMeasure μ] (hi : Integrable id μ) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r (Measure.map Prod.fst μ))-
      (∫ x, f x ∂compoundPoisson r (Measure.map Prod.snd μ))| ≤
      C*r*(∫ z,‖z.1-z.2‖ ∂μ) := by
  let A := ContinuousLinearMap.fst ℝ E E
  let B := ContinuousLinearMap.snd ℝ E E
  have hmA := compoundPoisson_map_linear r μ A
  have hmB := compoundPoisson_map_linear r μ B
  have hc := compoundPoisson_integrable_id r μ hi
  have hia : Integrable (fun z : E×E => f z.1) (compoundPoisson r μ) := by
    have hp : Integrable id (Measure.map A (compoundPoisson r μ)) :=
      (integrable_map_measure aestronglyMeasurable_id A.measurable.aemeasurable).mpr (A.integrable_comp hc)
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable A.measurable.aemeasurable).mp
      (integrable_lipschitz_of_id _ hp hf)
  have hib : Integrable (fun z : E×E => f z.2) (compoundPoisson r μ) := by
    have hp : Integrable id (Measure.map B (compoundPoisson r μ)) :=
      (integrable_map_measure aestronglyMeasurable_id B.measurable.aemeasurable).mpr (B.integrable_comp hc)
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable B.measurable.aemeasurable).mp
      (integrable_lipschitz_of_id _ hp hf)
  change |(∫ x, f x ∂compoundPoisson r (Measure.map A μ))-
    (∫ x, f x ∂compoundPoisson r (Measure.map B μ))| ≤ _
  rw [← hmA,← hmB,integral_map A.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable,
    integral_map B.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable]
  change |(∫ z : E×E, f z.1 ∂compoundPoisson r μ)-(∫ z, f z.2 ∂compoundPoisson r μ)|≤_
  rw [← integral_sub hia hib]
  calc
    _ ≤ ∫ z, |f z.1-f z.2| ∂compoundPoisson r μ := abs_integral_le_integral_abs
    _ ≤ ∫ z : E×E, (C:ℝ)*‖z.1-z.2‖ ∂compoundPoisson r μ := by
      apply integral_mono (hia.sub hib).abs
        (((A-B).integrable_comp hc).norm.const_mul (C:ℝ))
      intro z
      exact hf.norm_sub_le z.1 z.2
    _ = (C:ℝ)*(∫ z,‖z.1-z.2‖ ∂compoundPoisson r μ) := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (integral_norm_sub_compound r μ hi) C.coe_nonneg

end DilutedSpinGlass

end

end OAI
