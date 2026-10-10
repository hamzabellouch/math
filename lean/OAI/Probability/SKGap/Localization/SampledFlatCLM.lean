import Mathlib
import OAI.Probability.SKGap.Terminal.SingleSpinPlantedLaw
import OAI.Probability.SKGap.Localization.QueryColumn

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
namespace SKGapCutoff.Regression

lemma gaussian_add_constant {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) (c : ι → ℝ) :
    HasGaussianLaw (fun ω => X ω + c) μ := by
  have := hX.isGaussian_map
  refine ⟨by fun_prop, ?_⟩
  change IsGaussian (μ.map ((fun x : ι → ℝ => x+c) ∘ X))
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ι → ℝ => x+c) (μ.map X)) hX.aemeasurable]
  infer_instance

lemma piGaussian_coordinates {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ℝ≥0) :
    HasGaussianLaw (fun g : ι → ℝ => g) (Measure.pi (fun i => gaussianReal (m i) v)) :=
  (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).hasGaussianLaw
    (fun i => (measurePreserving_eval (fun j => gaussianReal (m j) v) i).hasLaw.hasGaussianLaw)

lemma piGaussian_coordinate_mean {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ℝ≥0) (i : ι) :
    (∫ g : ι → ℝ, g i ∂Measure.pi (fun j => gaussianReal (m j) v)) = m i := by
  rw [(measurePreserving_eval (fun j => gaussianReal (m j) v) i).hasLaw.integral_eq]
  exact integral_id_gaussianReal

lemma piGaussian_coordinate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (v : ℝ≥0) (i j : ι) :
    cov[fun g : ι → ℝ => g i, fun g => g j; Measure.pi (fun k => gaussianReal (m k) v)] =
      if i = j then (v:ℝ) else 0 := by
  by_cases h : i=j
  · subst j
    rw [covariance_self (measurePreserving_eval (fun k => gaussianReal (m k) v) i).aemeasurable,
      (measurePreserving_eval (fun k => gaussianReal (m k) v) i).hasLaw.variance_eq,
      variance_id_gaussianReal]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ => measurable_id.aemeasurable)).indepFun h).covariance_eq_zero
      (((piGaussian_coordinates m v).eval i).memLp_two)
      (((piGaussian_coordinates m v).eval j).memLp_two)

lemma upperCoefficient_min_max {n : ℕ} (x : Spin n) (i j : Fin n) (hij : i ≠ j) :
    upperCoefficient x (min i j,max i j) = spin x i * spin x j := by
  rcases lt_or_gt_of_ne hij with h|h
  · simp [upperCoefficient, min_eq_left h.le, max_eq_right h.le, h]
  · simp [upperCoefficient, min_eq_right h.le, max_eq_left h.le, h, mul_comm]

lemma minmax_pair_eq_iff {n : ℕ} (i j k l : Fin n) :
    (min i j,max i j) = (min k l,max k l) ↔ (i=k ∧ j=l) ∨ (i=l ∧ j=k) := by
  simp only [Prod.mk.injEq, min_def, max_def]
  split_ifs <;> omega

noncomputable def sampledFlatCLM (n : ℕ) : GaussianCoordinates n →L[ℝ] GaussianCoordinates n :=
  ContinuousLinearMap.pi fun p => if p.1 = p.2 then 0 else
    ContinuousLinearMap.proj (min p.1 p.2,max p.1 p.2)

@[simp] lemma sampledFlatCLM_apply {n : ℕ} (g : GaussianCoordinates n) (p : Fin n × Fin n) :
    sampledFlatCLM n g p = sampledInteraction g p.1 p.2 := by
  classical
  by_cases h : p.1=p.2 <;> simp [sampledFlatCLM, sampledInteraction, h]

noncomputable def plantedGOEArray {n : ℕ} (β : ℝ) (x : Spin n) (g : GaussianCoordinates n) :
    GaussianCoordinates n := fun p => if p.1=p.2 then 0 else
      β * goe g p.1 p.2 + β^2/(n:ℝ) * spin x p.1 * spin x p.2

noncomputable def offDiagonalGOECLM (n : ℕ) : GaussianCoordinates n →L[ℝ] GaussianCoordinates n :=
  ContinuousLinearMap.pi fun p => if p.1=p.2 then 0 else
    (Real.sqrt (2*n))⁻¹ • ((ContinuousLinearMap.proj p : GaussianCoordinates n →L[ℝ] ℝ) + ContinuousLinearMap.proj (p.2,p.1))

lemma plantedGOEArray_gaussian {n : ℕ} (β : ℝ) (x : Spin n) :
    HasGaussianLaw (plantedGOEArray β x) (standardArrayLaw (Fin n × Fin n)) := by
  have hh := gaussian_add_constant
    (coordinates_gaussian.map_fun (β • offDiagonalGOECLM n))
    (fun p : Fin n × Fin n => if p.1=p.2 then 0 else β^2/(n:ℝ)*spin x p.1*spin x p.2)
  apply hh.congr
  exact Eventually.of_forall (fun g => by
    ext p
    by_cases h : p.1=p.2
    · simp [offDiagonalGOECLM, plantedGOEArray, h]
    · simp only [offDiagonalGOECLM, plantedGOEArray, goe, h, ite_false,
        smul_apply, ContinuousLinearMap.pi_apply,
        add_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul]
      ring)

lemma sampled_planted_gaussian (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    HasGaussianLaw (fun g : GaussianCoordinates n => fun p : Fin n × Fin n =>
      sampledInteraction g p.1 p.2) (singleSpinPlantedLaw β x) := by
  rw [singleSpinPlantedLaw_eq_gaussianPi β hn]
  have hh := (piGaussian_coordinates (fun p => β^2/(n:ℝ)*upperCoefficient x p)
    (Real.toNNReal (β^2/(n:ℝ)))).map_fun (sampledFlatCLM n)
  exact hh.congr (Eventually.of_forall fun g => funext fun p => sampledFlatCLM_apply g p)

lemma plantedGOEArray_mean {n : ℕ} (β : ℝ) (x : Spin n) (p : Fin n × Fin n) :
    (∫ g, plantedGOEArray β x g p ∂standardArrayLaw (Fin n × Fin n)) =
      if p.1=p.2 then 0 else β^2/(n:ℝ)*spin x p.1*spin x p.2 := by
  by_cases h : p.1=p.2
  · simp [plantedGOEArray, h]
  · simp only [plantedGOEArray, h, ite_false]
    rw [integral_add (((goe_gaussian n).eval p.1 |>.eval p.2).integrable.const_mul β)
      (integrable_const _), integral_const_mul, goe_entry_mean]
    simp

lemma sampled_planted_mean (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) (p : Fin n × Fin n) :
    (∫ g, sampledInteraction g p.1 p.2 ∂singleSpinPlantedLaw β x) =
      if p.1=p.2 then 0 else β^2/(n:ℝ)*spin x p.1*spin x p.2 := by
  rw [singleSpinPlantedLaw_eq_gaussianPi β hn]
  by_cases h : p.1=p.2
  · simp [sampledInteraction, h]
  · simp only [sampledInteraction, h, ite_false]
    rw [piGaussian_coordinate_mean, upperCoefficient_min_max x _ _ h]
    ring

lemma plantedGOEArray_covariance {n : ℕ} (hn : 0 < n) (β : ℝ) (x : Spin n)
    (p q : Fin n × Fin n) :
    cov[fun g => plantedGOEArray β x g p, fun g => plantedGOEArray β x g q;
      standardArrayLaw (Fin n × Fin n)] =
      if p.1=p.2 ∨ q.1=q.2 then 0 else
        (β^2/(n:ℝ)) * ((if p.1=q.1 ∧ p.2=q.2 then 1 else 0) +
          (if p.1=q.2 ∧ p.2=q.1 then 1 else 0)) := by
  by_cases hp : p.1=p.2
  · simp [plantedGOEArray, hp]
  by_cases hq : q.1=q.2
  · simp [plantedGOEArray, hq]
  simp only [plantedGOEArray, hp, hq, false_or, ite_false]
  rw [covariance_add_const_left (((goe_gaussian n).eval p.1 |>.eval p.2).integrable.const_mul β),
    covariance_add_const_right (((goe_gaussian n).eval q.1 |>.eval q.2).integrable.const_mul β),
    covariance_const_mul_left, covariance_const_mul_right, goe_entry_covariance hn]
  ring

lemma sampled_planted_covariance (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n)
    (p q : Fin n × Fin n) :
    cov[fun g => sampledInteraction g p.1 p.2, fun g => sampledInteraction g q.1 q.2;
        singleSpinPlantedLaw β x] =
      if p.1=p.2 ∨ q.1=q.2 then 0 else
        (β^2/(n:ℝ)) * ((if p.1=q.1 ∧ p.2=q.2 then 1 else 0) +
          (if p.1=q.2 ∧ p.2=q.1 then 1 else 0)) := by
  rw [singleSpinPlantedLaw_eq_gaussianPi β hn]
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
  · rw [ite_eq_right (not_or.mpr ⟨h1,h2⟩), ite_eq_right h1, ite_eq_right h2,
      add_zero, mul_zero]

lemma planted_matrix_representation (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    (singleSpinPlantedLaw β x).map (fun g : GaussianCoordinates n =>
      fun p : Fin n × Fin n => sampledInteraction g p.1 p.2) =
    (standardArrayLaw (Fin n × Fin n)).map (plantedGOEArray β x) := by
  apply gaussian_vector_law_ext (sampled_planted_gaussian β hn x) (plantedGOEArray_gaussian β x)
  · intro p
    rw [sampled_planted_mean β hn, plantedGOEArray_mean]
  · intro p q
    rw [sampled_planted_covariance β hn, plantedGOEArray_covariance hn]

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

end

end OAI
