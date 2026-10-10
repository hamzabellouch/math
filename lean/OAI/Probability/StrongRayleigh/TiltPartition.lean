import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

lemma sum_atomMass [DecidableEq F] (μ : ProbabilityMeasure (F → Bool)) :
    ∑ x : F → Bool, ((μ : Measure (F → Bool)) {x}).toReal = 1 := by
  classical
  rw [← ENNReal.toReal_sum]
  · simp
  · intro x hx
    exact measure_ne_top _ _

lemma exists_atomMass_pos (μ : ProbabilityMeasure (F → Bool)) :
    ∃ x : F → Bool, 0 < ((μ : Measure (F → Bool)) {x}).toReal := by
  classical
  have h := sum_atomMass μ
  have hp : 0 < ∑ x : F → Bool, ((μ : Measure (F → Bool)) {x}).toReal := by
    rw [h]
    norm_num
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x hx => ENNReal.toReal_nonneg)).mp hp
  exact ⟨x, hx⟩

lemma tiltPartition_pos (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) :
    0 < tiltPartition μ h := by
  classical
  obtain ⟨x, hx⟩ := exists_atomMass_pos μ
  unfold tiltPartition
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  · exact ⟨x, Finset.mem_univ x, mul_pos (Real.exp_pos _) hx⟩

lemma tiltPartition_ne_zero (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) :
    tiltPartition μ h ≠ 0 := ne_of_gt (tiltPartition_pos μ h)

end Problem336AdditiveD139

end

end OAI
