import Mathlib
import OAI.Probability.SKGap.Localization.SampledFlatCLM
import OAI.Probability.SKGap.Matrix.DoublePlantLogNorm

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
namespace SKGapCutoff.Regression

noncomputable def doublePlantedGOEArray {n : ℕ} (β : ℝ) (x y : Spin n)
    (g : GaussianCoordinates n) : GaussianCoordinates n :=
  plantedGOEArray β x g + fun p => if p.1=p.2 then 0 else β^2/(n:ℝ)*spin y p.1*spin y p.2

lemma doublePlantedGOEArray_gaussian {n : ℕ} (β : ℝ) (x y : Spin n) :
    HasGaussianLaw (doublePlantedGOEArray β x y) (standardArrayLaw (Fin n × Fin n)) :=
  gaussian_add_constant (plantedGOEArray_gaussian β x) _

lemma sampled_double_planted_gaussian (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n) :
    HasGaussianLaw (fun g : GaussianCoordinates n => fun p : Fin n × Fin n =>
      sampledInteraction g p.1 p.2) (doubleSpinPlantedLaw β x y) := by
  rw [doubleSpinPlantedLaw_eq_gaussianPi β hn]
  have hh := (piGaussian_coordinates (fun p => β^2/(n:ℝ)*(upperCoefficient x p + upperCoefficient y p))
    (Real.toNNReal (β^2/(n:ℝ)))).map_fun (sampledFlatCLM n)
  exact hh.congr (Eventually.of_forall fun g => funext fun p => sampledFlatCLM_apply g p)

lemma doublePlantedGOEArray_mean {n : ℕ} (β : ℝ) (x y : Spin n) (p : Fin n × Fin n) :
    (∫ g, doublePlantedGOEArray β x y g p ∂standardArrayLaw (Fin n × Fin n)) =
      if p.1=p.2 then 0 else β^2/(n:ℝ)*(spin x p.1*spin x p.2+spin y p.1*spin y p.2) := by
  change (∫ g, plantedGOEArray β x g p + _ ∂standardArrayLaw (Fin n × Fin n)) = _
  rw [integral_add ((plantedGOEArray_gaussian β x).eval p).integrable
    (integrable_const _), plantedGOEArray_mean, integral_const]
  by_cases h : p.1=p.2
  · simp [h]
  · simp [h]
    ring

lemma sampled_double_planted_mean (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n)
    (p : Fin n × Fin n) :
    (∫ g, sampledInteraction g p.1 p.2 ∂doubleSpinPlantedLaw β x y) =
      if p.1=p.2 then 0 else β^2/(n:ℝ)*(spin x p.1*spin x p.2+spin y p.1*spin y p.2) := by
  rw [doubleSpinPlantedLaw_eq_gaussianPi β hn]
  by_cases h : p.1=p.2
  · simp [sampledInteraction, h]
  · simp only [sampledInteraction, h, ite_false]
    rw [piGaussian_coordinate_mean, upperCoefficient_min_max x _ _ h,
      upperCoefficient_min_max y _ _ h]

lemma doublePlantedGOEArray_covariance {n : ℕ} (hn : 0 < n) (β : ℝ) (x y : Spin n)
    (p q : Fin n × Fin n) :
    cov[fun g => doublePlantedGOEArray β x y g p, fun g => doublePlantedGOEArray β x y g q;
      standardArrayLaw (Fin n × Fin n)] =
      if p.1=p.2 ∨ q.1=q.2 then 0 else
        (β^2/(n:ℝ)) * ((if p.1=q.1 ∧ p.2=q.2 then 1 else 0) +
          (if p.1=q.2 ∧ p.2=q.1 then 1 else 0)) := by
  change cov[fun g => plantedGOEArray β x g p + _, fun g => plantedGOEArray β x g q + _; _] = _
  rw [covariance_add_const_left ((plantedGOEArray_gaussian β x).eval p).integrable,
    covariance_add_const_right ((plantedGOEArray_gaussian β x).eval q).integrable,
    plantedGOEArray_covariance hn]

lemma sampled_double_planted_covariance (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n)
    (p q : Fin n × Fin n) :
    cov[fun g => sampledInteraction g p.1 p.2, fun g => sampledInteraction g q.1 q.2;
        doubleSpinPlantedLaw β x y] =
      if p.1=p.2 ∨ q.1=q.2 then 0 else
        (β^2/(n:ℝ)) * ((if p.1=q.1 ∧ p.2=q.2 then 1 else 0) +
          (if p.1=q.2 ∧ p.2=q.1 then 1 else 0)) := by
  rw [doubleSpinPlantedLaw_eq_gaussianPi β hn]
  by_cases hp : p.1=p.2
  · simp [sampledInteraction, hp]
  by_cases hq : q.1=q.2
  · simp [sampledInteraction, hq]
  simp only [sampledInteraction, hp, hq, false_or, ite_false]
  rw [piGaussian_coordinate_covariance, Real.coe_toNNReal _ (by positivity)]
  simp only [minmax_pair_eq_iff]
  by_cases h1 : p.1=q.1 ∧ p.2=q.2
  · have h2 : ¬ (p.1=q.2 ∧ p.2=q.1) := by omega
    rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right h2, add_zero, mul_one]
  by_cases h2 : p.1=q.2 ∧ p.2=q.1
  · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_left h2, zero_add, mul_one]
  · rw [ite_eq_right (not_or.mpr ⟨h1,h2⟩), ite_eq_right h1, ite_eq_right h2, add_zero, mul_zero]

lemma double_planted_matrix_representation (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n) :
    (doubleSpinPlantedLaw β x y).map (fun g : GaussianCoordinates n =>
      fun p : Fin n × Fin n => sampledInteraction g p.1 p.2) =
    (standardArrayLaw (Fin n × Fin n)).map (doublePlantedGOEArray β x y) := by
  apply gaussian_vector_law_ext (sampled_double_planted_gaussian β hn x y)
    (doublePlantedGOEArray_gaussian β x y)
  · intro p
    rw [sampled_double_planted_mean β hn, doublePlantedGOEArray_mean]
  · intro p q
    rw [sampled_double_planted_covariance β hn, doublePlantedGOEArray_covariance hn]

end SKGapCutoff.Regression

end

end OAI
