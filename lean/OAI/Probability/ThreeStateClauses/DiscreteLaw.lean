import Mathlib
import OAI.Probability.ThreeStateClauses.PosteriorLaw

namespace OAI

/-! Discrete Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α : Type*}

def uniformSpin : PMF (Fin 3) := PMF.ofFintype (fun _ ↦ (1/3 : ℝ≥0∞)) (by
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

@[simp] lemma uniformSpin_apply (i : Fin 3) : uniformSpin i = (1/3 : ℝ≥0∞) := rfl

def discreteMarginal (p : Fin 3 → PMF α) : PMF α := uniformSpin.bind p

def discreteWeight (p : Fin 3 → PMF α) (a : α) : ℝ := avg (fun i ↦ (p i a).toReal)

lemma discreteWeight_nonneg (p : Fin 3 → PMF α) (a : α) : 0 ≤ discreteWeight p a := by
  unfold discreteWeight avg; positivity

lemma discreteMarginal_apply (p : Fin 3 → PMF α) (a : α) :
    discreteMarginal p a = (p 0 a+p 1 a+p 2 a)/3 := by
  simp [discreteMarginal, PMF.bind_apply, tsum_fintype, Fin.sum_univ_three, div_eq_mul_inv]
  ring

lemma discreteMarginal_real (p : Fin 3 → PMF α) (a : α) :
    (discreteMarginal p a).toReal = discreteWeight p a := by
  rw [discreteMarginal_apply, ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨(p 0).apply_ne_top a, (p 1).apply_ne_top a⟩)
      ((p 2).apply_ne_top a),
    ENNReal.toReal_add ((p 0).apply_ne_top a) ((p 1).apply_ne_top a)]
  norm_num [discreteWeight, avg]

lemma discreteWeight_zero (p : Fin 3 → PMF α) (a : α) (h : discreteWeight p a = 0) (i : Fin 3) :
    (p i a).toReal = 0 := by
  dsimp [discreteWeight, avg] at h
  fin_cases i <;> dsimp <;> linarith [ENNReal.toReal_nonneg (a := p 0 a),
    ENNReal.toReal_nonneg (a := p 1 a), ENNReal.toReal_nonneg (a := p 2 a)]

def discreteMessage (p : Fin 3 → PMF α) (a : α) : Message := by
  by_cases h : discreteWeight p a = 0
  · exact ⟨fun _ ↦ 1, fun _ ↦ by norm_num, by norm_num [avg]⟩
  · refine ⟨fun i ↦ (p i a).toReal/discreteWeight p a, fun _ ↦ div_nonneg (by positivity)
      (discreteWeight_nonneg p a), ?_⟩
    change ((p 0 a).toReal/discreteWeight p a+(p 1 a).toReal/discreteWeight p a+
      (p 2 a).toReal/discreteWeight p a)/3 = 1
    rw [← add_div, ← add_div, div_div, mul_comm]
    have hw : (p 0 a).toReal+(p 1 a).toReal+(p 2 a).toReal = 3*discreteWeight p a := by
      dsimp [discreteWeight, avg]; ring
    rw [hw, div_self (mul_ne_zero (by norm_num) h)]

lemma discrete_bayes (p : Fin 3 → PMF α) (a : α) (i : Fin 3) :
    discreteWeight p a*(discreteMessage p a).1 i = (p i a).toReal := by
  unfold discreteMessage
  split_ifs with h
  · simpa [h] using (discreteWeight_zero p a h i).symm
  · exact mul_div_cancel₀ _ h

lemma discrete_coord {p : Fin 3 → PMF α} {a : α} (h : discreteWeight p a ≠ 0) (i : Fin 3) :
    (discreteMessage p a).1 i = (p i a).toReal/discreteWeight p a := by
  simp only [discreteMessage, dite_eq_right h]

lemma pmf_real_sum (p : PMF α) : ∑' a, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe]
  norm_num

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma discreteCoordinate_integrable (p : Fin 3 → PMF α) (i : Fin 3) :
    Integrable (fun a ↦ (discreteMessage p a).1 i) (discreteMarginal p).toMeasure :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 3
    (Filter.Eventually.of_forall (fun a ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (coordinate_nonneg _ _)]
      exact coordinate_le_three _ _))

def discreteProbability (p : Fin 3 → PMF α) : ProbabilityMeasure Message :=
  ProbabilityMeasure.map (⟨(discreteMarginal p).toMeasure, inferInstance⟩ : ProbabilityMeasure α)
    (discreteMessage p)

lemma integral_discreteProbability (p : Fin 3 → PMF α) {f : Message → ℝ} (hf : Measurable f) :
    (∫ m, f m ∂(discreteProbability p).toMeasure) =
      ∫ a, f (discreteMessage p a) ∂(discreteMarginal p).toMeasure := by
  change (∫ m, f m ∂Measure.map (discreteMessage p) (discreteMarginal p).toMeasure) = _
  exact integral_map (measurable_of_countable _).aemeasurable hf.aestronglyMeasurable

lemma discreteProbability_balanced (p : Fin 3 → PMF α) (i : Fin 3) :
    (∫ m, m.1 i ∂(discreteProbability p).toMeasure) = 1 := by
  rw [integral_discreteProbability p (continuous_coordinate i).measurable,
    PMF.integral_eq_tsum _ _ (discreteCoordinate_integrable p i)]
  simpa only [smul_eq_mul, discreteMarginal_real, discrete_bayes] using pmf_real_sum (p i)

end Measures

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma pmf_bounded_integrable (p : PMF α) {f : α → ℝ} {C : ℝ} (hf : ∀ a, |f a| ≤ C) :
    Integrable f p.toMeasure :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun a ↦ by simpa only [Real.norm_eq_abs] using hf a))

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSingletonClass β] in
lemma pmf_measure_bind (p : PMF α) (K : α → PMF β) :
    (p.bind K).toMeasure = Measure.sum (fun a ↦ p a • (K a).toMeasure) := by
  apply Measure.ext
  intro s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]

lemma integral_pmf_bind (p : PMF α) (K : α → PMF β) {f : β → ℝ} {C : ℝ}
    (hf : ∀ b, |f b| ≤ C) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by
  have hi := pmf_bounded_integrable (p.bind K) hf
  rw [pmf_measure_bind] at hi ⊢
  rw [integral_sum_measure hi]
  simp only [integral_smul_measure, smul_eq_mul]
  rw [PMF.integral_eq_tsum]
  · rfl
  · apply pmf_bounded_integrable
    intro a
    calc
      |∫ b, f b ∂(K a).toMeasure| ≤ ∫ b, |f b| ∂(K a).toMeasure := abs_integral_le_integral_abs
      _ ≤ ∫ _, C ∂(K a).toMeasure := integral_mono (pmf_bounded_integrable (K a) hf).abs
        (integrable_const C) hf
      _ = C := by simp

lemma integral_pmf_map (p : PMF α) (T : α → β) (f : β → ℝ) :
    (∫ b, f b ∂(p.map T).toMeasure) = ∫ a, f (T a) ∂p.toMeasure := by
  rw [← PMF.toMeasure_map T p (measurable_of_countable T)]
  exact integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

lemma discrete_bayes_integral (p : Fin 3 → PMF α) (i : Fin 3) {g : α → ℝ} {C : ℝ}
    (hg : ∀ a, |g a| ≤ C) :
    (∫ a, (discreteMessage p a).1 i*g a ∂(discreteMarginal p).toMeasure) =
      ∫ a, g a ∂(p i).toMeasure := by
  rw [PMF.integral_eq_tsum, PMF.integral_eq_tsum _ _ (pmf_bounded_integrable (p i) hg)]
  · apply tsum_congr
    intro a
    simp only [smul_eq_mul, discreteMarginal_real, ← mul_assoc, discrete_bayes]
  · apply pmf_bounded_integrable (C := 3*C)
    intro a
    rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]
    exact mul_le_mul (coordinate_le_three _ _) (hg a) (abs_nonneg _) (by norm_num)

end ThreeState.TreeClauses.Experiment

end

end OAI
