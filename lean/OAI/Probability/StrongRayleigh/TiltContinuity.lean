import OAI.Probability.StrongRayleigh.TiltPartition

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

lemma continuous_tiltPartition (μ : ProbabilityMeasure (F → Bool)) :
    Continuous (tiltPartition μ) := by
  classical
  unfold tiltPartition
  fun_prop

lemma continuous_tiltMean (μ : ProbabilityMeasure (F → Bool)) (i : F) :
    Continuous (fun h : F → ℝ => tiltMean μ h i) := by
  classical
  unfold tiltMean
  apply Continuous.div
  · fun_prop
  · exact continuous_tiltPartition μ
  · exact tiltPartition_ne_zero μ

lemma continuous_tiltSecondMoment (μ : ProbabilityMeasure (F → Bool)) (i j : F) :
    Continuous (fun h : F → ℝ => tiltSecondMoment μ h i j) := by
  classical
  unfold tiltSecondMoment
  apply Continuous.div
  · fun_prop
  · exact continuous_tiltPartition μ
  · exact tiltPartition_ne_zero μ

lemma continuous_tiltCovariance (μ : ProbabilityMeasure (F → Bool)) (i j : F) :
    Continuous (fun h : F → ℝ => tiltCovariance μ h i j) := by
  exact (continuous_tiltSecondMoment μ i j).sub
    ((continuous_tiltMean μ i).mul (continuous_tiltMean μ j))

lemma measurable_tiltPartition (μ : ProbabilityMeasure (F → Bool)) :
    Measurable (tiltPartition μ) := (continuous_tiltPartition μ).measurable

lemma measurable_tiltMean (μ : ProbabilityMeasure (F → Bool)) (i : F) :
    Measurable (fun h : F → ℝ => tiltMean μ h i) :=
  (continuous_tiltMean μ i).measurable

lemma measurable_tiltSecondMoment (μ : ProbabilityMeasure (F → Bool)) (i j : F) :
    Measurable (fun h : F → ℝ => tiltSecondMoment μ h i j) :=
  (continuous_tiltSecondMoment μ i j).measurable

lemma measurable_tiltCovariance (μ : ProbabilityMeasure (F → Bool)) (i j : F) :
    Measurable (fun h : F → ℝ => tiltCovariance μ h i j) :=
  (continuous_tiltCovariance μ i j).measurable

end Problem336AdditiveD139

end

end OAI
