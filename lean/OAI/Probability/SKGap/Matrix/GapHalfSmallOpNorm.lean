import Mathlib
import OAI.Probability.SKGap.Localization.GeneratorNonposMax
import OAI.Probability.SKGap.Gaussian.SampledInnerTailScaled

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
namespace SKGapCutoff

theorem hasGap_half_of_small_opNorm {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (hJC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ (1:ℝ)/8) :
    HasGap J (1/2) := by
  have hg := hasGap_of_opNorm J hJ hdiag (1/8) (by norm_num) hJC
  have he : Real.exp (8*((1:ℝ)/8)) ≤ 3 := by norm_num; exact Real.exp_one_lt_three.le
  have hc : (1:ℝ)/2 ≤ 1-1/8-4*(1/8)^2-4*Real.exp (8*(1/8))*(1/8)^2 := by
    norm_num at he ⊢
    linarith
  intro f
  have hv : 0 ≤ gibbsVariance J f := by
    unfold gibbsVariance gibbsExpectation
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (gibbs_pos J x).le (sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right hc hv).trans (hg f)

theorem quenchedGap_small_beta (β : ℝ) (hβ : 0 < β) (hβ' : β ≤ 1/176) :
    QuenchedGap β := by
  have hsmall : 2*(11*β) ≤ (1:ℝ)/8 := by linarith
  have hbad : Tendsto (fun n => disorderLaw β n
      {g | ¬ HasGap (sampledInteraction g) (1/2)}) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (RandomMatrix.sampled_opNorm_tendsto_scaled β hβ)
      (Eventually.of_forall (fun _ => bot_le))
    apply Eventually.of_forall
    intro n
    apply measure_mono
    intro g hg
    by_contra hnot
    apply hg
    exact hasGap_half_of_small_opNorm (sampledInteraction g) (sampledInteraction_symm g)
      (sampledInteraction_diag g) ((le_of_not_gt hnot).trans hsmall)
  refine ⟨1/2, by norm_num, ?_⟩
  have hl := (ENNReal.continuous_sub_left (by simp : (1:ℝ≥0∞) ≠ ∞)).continuousAt.tendsto.comp hbad
  have he (n : ℕ) : disorderLaw β n {g | HasGap (sampledInteraction g) (1/2)} =
      1-disorderLaw β n {g | ¬ HasGap (sampledInteraction g) (1/2)} := by
    let : IsProbabilityMeasure (disorderLaw β n) := by unfold disorderLaw; infer_instance
    have hh := measure_compl (μ := disorderLaw β n) (measurableSet_sampledGap n (1/2)).compl
      (measure_ne_top _ _)
    simpa only [Set.compl_ofPred,not_not,measure_univ] using hh
  simpa only [Function.comp_def,tsub_zero,← he] using hl

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
