import OAI.Probability.StrongRayleigh.TiltPartition

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Problem336AdditiveD139

lemma boolReal_nonneg (b : Bool) : 0 ≤ boolReal b := by cases b <;> norm_num [boolReal]
lemma boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by cases b <;> norm_num [boolReal]
lemma boolReal_mul_self (b : Bool) : boolReal b * boolReal b = boolReal b := by
  cases b <;> norm_num [boolReal]

lemma tiltMean_nonneg {F : Type u_1} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    0 ≤ tiltMean μ h i := by
  classical
  apply div_nonneg _ (tiltPartition_pos μ h).le
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
    (boolReal_nonneg _)

lemma tiltMean_le_one {F : Type u_2} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltMean μ h i ≤ 1 := by
  classical
  unfold tiltMean
  apply (div_le_one (tiltPartition_pos μ h)).2
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_of_le_one_right
    (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (boolReal_le_one _)

lemma tiltSecondMoment_self {F : Type u_3} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltSecondMoment μ h i i = tiltMean μ h i := by
  classical
  simp only [tiltSecondMoment, tiltMean, mul_assoc, boolReal_mul_self]

lemma tiltCovariance_self {F : Type u_4} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltCovariance μ h i i = tiltMean μ h i * (1 - tiltMean μ h i) := by
  rw [tiltCovariance, tiltSecondMoment_self]
  ring

lemma tiltCovariance_self_nonneg {F : Type u_5} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    0 ≤ tiltCovariance μ h i i := by
  rw [tiltCovariance_self]
  exact mul_nonneg (tiltMean_nonneg μ h i) (sub_nonneg.mpr (tiltMean_le_one μ h i))

lemma twice_tilt_variance_le_half {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2 := by
  nlinarith [sq_nonneg (tiltMean μ h i - 1 / 2)]

end Problem336AdditiveD139

end

end OAI
