import Mathlib

namespace OAI

/-! Poisson Moments. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Probability

def poissonWeight (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t)*t^n/(n.factorial:ℝ)

lemma poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight t n := by
  unfold poissonWeight; positivity

lemma poissonWeight_mass (t : ℝ≥0) : HasSum (poissonWeight t) 1 :=
  hasSum_one_poissonMeasure t

def _root_.OAI.ThreeState.TreeClauses.poissonPMF (rate : ℝ≥0) : PMF ℕ := by
  refine ⟨fun count ↦ ENNReal.ofReal (poissonWeight rate count), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact (poissonWeight_mass rate).toNNReal (poissonWeight_nonneg rate.coe_nonneg)

lemma poissonWeight_succ (t : ℝ) (n : ℕ) :
    poissonWeight t (n+1)*((n:ℝ)+1) = t*poissonWeight t n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma poissonWeight_mean (t : ℝ≥0) : HasSum (fun n ↦ poissonWeight t n*(n:ℝ)) t := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero,
    Nat.cast_add, Nat.cast_one, poissonWeight_succ]
  simpa using (poissonWeight_mass t).mul_left (t:ℝ)

lemma poissonWeight_factorial_second (t : ℝ≥0) :
    HasSum (fun n ↦ poissonWeight t n*((n:ℝ)^2-n)) ((t:ℝ)^2) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    sub_self, mul_zero, sub_zero]
  have he (n : ℕ) : poissonWeight t (n+1)*(((n+1:ℕ):ℝ)^2-((n+1:ℕ):ℝ)) =
      (t:ℝ)*(poissonWeight t n*(n:ℝ)) := by
    push_cast
    calc
      _ = (poissonWeight t (n+1)*((n:ℝ)+1))*(n:ℝ) := by ring
      _ = _ := by rw [poissonWeight_succ]; ring
  simp_rw [he]
  simpa [pow_two] using (poissonWeight_mean t).mul_left (t:ℝ)

lemma poissonWeight_second (t : ℝ≥0) :
    HasSum (fun n ↦ poissonWeight t n*(n:ℝ)^2) ((t:ℝ)^2+t) := by
  have h := (poissonWeight_factorial_second t).add (poissonWeight_mean t)
  convert h using 1
  ext n; ring

lemma poissonPMF_real (t : ℝ≥0) (n : ℕ) : (poissonPMF t n).toReal = poissonWeight t n := by
  change (ENNReal.ofReal (poissonWeight t n)).toReal = _
  exact ENNReal.toReal_ofReal (poissonWeight_nonneg t.coe_nonneg n)

lemma poissonPMF_toMeasure (t : ℝ≥0) : (poissonPMF t).toMeasure = poissonMeasure t := by
  apply Measure.ext_of_singleton
  intro n
  rw [PMF.toMeasure_apply_singleton, poissonMeasure_singleton]
  · rfl
  · exact measurableSet_singleton n

lemma poisson_integrable_first (t : ℝ≥0) : Integrable (fun n : ℕ ↦ (n:ℝ)) (poissonPMF t).toMeasure := by
  rw [poissonPMF_toMeasure, integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, Nat.abs_cast, smul_eq_mul, poissonWeight] using (poissonWeight_mean t).summable

lemma poisson_integrable_second (t : ℝ≥0) : Integrable (fun n : ℕ ↦ (n:ℝ)^2) (poissonPMF t).toMeasure := by
  rw [poissonPMF_toMeasure, integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, abs_pow, Nat.abs_cast, smul_eq_mul, poissonWeight] using (poissonWeight_second t).summable

lemma poisson_integral_first (t : ℝ≥0) : (∫ n : ℕ, (n:ℝ) ∂(poissonPMF t).toMeasure) = t := by
  rw [PMF.integral_eq_tsum _ _ (poisson_integrable_first t)]
  simpa only [poissonPMF_real, smul_eq_mul] using (poissonWeight_mean t).tsum_eq

lemma poisson_integral_second (t : ℝ≥0) : (∫ n : ℕ, (n:ℝ)^2 ∂(poissonPMF t).toMeasure) = (t:ℝ)^2+t := by
  rw [PMF.integral_eq_tsum _ _ (poisson_integrable_second t)]
  simpa only [poissonPMF_real, smul_eq_mul] using (poissonWeight_second t).tsum_eq

lemma poisson_integral_factorial_second (t : ℝ≥0) :
    (∫ n : ℕ, ((n:ℝ)^2-n) ∂(poissonPMF t).toMeasure) = (t:ℝ)^2 := by
  rw [integral_sub (poisson_integrable_second t) (poisson_integrable_first t),
    poisson_integral_second, poisson_integral_first]
  ring

end ThreeState.TreeClauses.Probability

end

end OAI
