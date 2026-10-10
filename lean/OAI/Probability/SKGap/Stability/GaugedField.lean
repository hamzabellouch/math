import Mathlib
import OAI.Probability.SKGap.Localization.SampledFlatCLM

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
namespace SKGapCutoff.Regression

noncomputable def gaugedField {n : ℕ} (x : Spin n) (g : GaussianCoordinates n) : Fin n → ℝ :=
  fun i => spin x i * field (sampledInteraction g) x i

noncomputable def gaugeFieldCLM {n : ℕ} (x : Spin n) : GaussianCoordinates n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j, (spin x i * spin x j) •
    (ContinuousLinearMap.proj (i,j) : GaussianCoordinates n →L[ℝ] ℝ)

lemma gaugeFieldCLM_sampled {n : ℕ} (x : Spin n) (g : GaussianCoordinates n) :
    gaugeFieldCLM x (fun p => sampledInteraction g p.1 p.2) = gaugedField x g := by
  ext i
  simp [gaugeFieldCLM, gaugedField, field, Finset.mul_sum, mul_left_comm, mul_comm]

lemma gaugedField_gaussian (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    HasGaussianLaw (gaugedField x) (singleSpinPlantedLaw β x) := by
  exact ((sampled_planted_gaussian β hn x).map_fun (gaugeFieldCLM x)).congr
    (Eventually.of_forall (gaugeFieldCLM_sampled x))

lemma sum_off_diagonal_const {n : ℕ} (i : Fin n) (c : ℝ) :
    (∑ j : Fin n, if i=j then 0 else c) = ((n:ℝ)-1)*c := by
  have he (j : Fin n) : (if i=j then (0:ℝ) else c) = c - if j=i then c else 0 := by
    by_cases h : i=j <;> simp [h, eq_comm]
  simp_rw [he]
  simp [Finset.sum_sub_distrib]
  ring

lemma gaugedField_mean (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) (i : Fin n) :
    (∫ g, gaugedField x g i ∂singleSpinPlantedLaw β x) = β^2*((n:ℝ)-1)/(n:ℝ) := by
  unfold gaugedField field
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_mul_const]
    have hm (j : Fin n) := sampled_planted_mean β hn x (i,j)
    simp only at hm
    simp_rw [hm]
    rw [Finset.mul_sum]
    have he (j : Fin n) : spin x i *
        ((if i=j then 0 else β^2/(n:ℝ)*spin x i*spin x j)*spin x j) =
        if i=j then 0 else β^2/(n:ℝ) := by
      by_cases h : i=j
      · simp [h]
      · simp only [h, ite_false]
        have h1 := spin_sq x i
        have h2 := spin_sq x j
        nlinarith [congrArg (fun a : ℝ => β^2/(n:ℝ)*a) (show (spin x i*spin x j)^2=1 by simp [mul_pow])]
    simp_rw [he]
    rw [sum_off_diagonal_const]
    ring
  · intro j _
    exact (((sampled_planted_gaussian β hn x).eval (i,j)).integrable.mul_const _)

lemma gauged_entry_covariance (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n)
    (i j k l : Fin n) :
    cov[fun g => spin x i*spin x j*sampledInteraction g i j,
      fun g => spin x k*spin x l*sampledInteraction g k l; singleSpinPlantedLaw β x] =
      if i=j ∨ k=l then 0 else β^2/(n:ℝ)*
        ((if i=k ∧ j=l then 1 else 0)+(if i=l ∧ j=k then 1 else 0)) := by
  rw [covariance_const_mul_left, covariance_const_mul_right, sampled_planted_covariance β hn x (i,j) (k,l)]
  by_cases h : i=j ∨ k=l
  · simp [h]
  rw [ite_eq_right h]
  by_cases h1 : i=k ∧ j=l
  · rcases h1 with ⟨hik,hjl⟩
    subst k
    subst l
    have h2 : ¬ (i=j ∧ j=i) := fun h' => h (Or.inl h'.1)
    rw [ite_eq_left ⟨rfl,rfl⟩, ite_eq_right h2, add_zero, mul_one]
    calc
      _ = (β^2/(n:ℝ))*(spin x i*spin x j)^2 := by ring
      _ = _ := by simp [mul_pow]
  by_cases h2 : i=l ∧ j=k
  · rcases h2 with ⟨hil,hjk⟩
    subst l
    subst k
    rw [ite_eq_right h1, ite_eq_left ⟨rfl,rfl⟩, zero_add, mul_one]
    calc
      _ = (β^2/(n:ℝ))*(spin x i*spin x j)^2 := by ring
      _ = _ := by simp [mul_pow]
  · rw [ite_eq_right h1, ite_eq_right h2]
    ring

lemma sum_covariance_pattern {n : ℕ} (i k : Fin n) (c : ℝ) :
    (∑ j : Fin n, ∑ l : Fin n, if i=j ∨ k=l then 0 else c*
      ((if i=k ∧ j=l then (1:ℝ) else 0)+(if i=l ∧ j=k then 1 else 0))) =
      if i=k then c*((n:ℝ)-1) else c := by
  by_cases h : i=k
  · subst k
    have he (j l : Fin n) :
        (if i=j ∨ i=l then 0 else c*((if i=i ∧ j=l then (1:ℝ) else 0)+
           (if i=l ∧ j=i then 1 else 0))) = if j=l then (if i=j then 0 else c) else 0 := by
      by_cases hj : i=j <;> by_cases hl : i=l <;> by_cases hjl : j=l <;> simp [hj,hl,hjl]
    calc
      _ = ∑ j : Fin n, ∑ l : Fin n, if j=l then (if i=j then 0 else c) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        exact he j l
      _ = _ := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [sum_off_diagonal_const]
        ring
  · have he (j l : Fin n) :
        (if i=j ∨ k=l then 0 else c*((if i=k ∧ j=l then (1:ℝ) else 0)+
           (if i=l ∧ j=k then 1 else 0))) = if j=k then (if l=i then c else 0) else 0 := by
      by_cases hj : j=k <;> by_cases hl : l=i <;> simp_all [eq_comm]
    simp_rw [he]
    simp [h]

lemma gaugedField_covariance (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) (i k : Fin n) :
    cov[fun g => gaugedField x g i, fun g => gaugedField x g k; singleSpinPlantedLaw β x] =
      if i=k then β^2*((n:ℝ)-1)/(n:ℝ) else β^2/(n:ℝ) := by
  have he (i : Fin n) (g : GaussianCoordinates n) : gaugedField x g i =
      ∑ j, (spin x i*spin x j)*sampledInteraction g i j := by
    simp [gaugedField, field, Finset.mul_sum, mul_left_comm, mul_comm]
  let := singleSpinPlantedLaw_probability β hn x
  simp_rw [he]
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [gauged_entry_covariance β hn, sum_covariance_pattern]
    split_ifs <;> ring
  · exact fun j => ((sampled_planted_gaussian β hn x).eval (i,j)).memLp_two.const_mul _
  · exact fun l => ((sampled_planted_gaussian β hn x).eval (k,l)).memLp_two.const_mul _

noncomputable def sharedGaussianField {n : ℕ} (m a b : ℝ)
    (g : Option (Fin n) → ℝ) : Fin n → ℝ := fun i => m + a*g (some i) + b*g none

noncomputable def sharedGaussianFieldCLM (n : ℕ) (a b : ℝ) :
    (Option (Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => a •
    (ContinuousLinearMap.proj (some i) : (Option (Fin n) → ℝ) →L[ℝ] ℝ) +
      b • ContinuousLinearMap.proj none

lemma sharedGaussianField_gaussian (n : ℕ) (m a b : ℝ) :
    HasGaussianLaw (sharedGaussianField (n := n) m a b) (standardArrayLaw (Option (Fin n))) := by
  have hh := gaussian_add_constant (coordinates_gaussian.map_fun (sharedGaussianFieldCLM n a b))
    (fun _ : Fin n => m)
  apply hh.congr
  exact Eventually.of_forall fun g => by
    ext i
    simp [sharedGaussianFieldCLM, sharedGaussianField]
    ring

lemma sharedGaussianField_mean {n : ℕ} (m a b : ℝ) (i : Fin n) :
    (∫ g, sharedGaussianField m a b g i ∂standardArrayLaw (Option (Fin n))) = m := by
  have ha := (coordinate_hasLaw (some i)).hasGaussianLaw.integrable.const_mul a
  have hb := (coordinate_hasLaw (none : Option (Fin n))).hasGaussianLaw.integrable.const_mul b
  simp only [sharedGaussianField]
  have hai : Integrable (fun g : Option (Fin n) → ℝ => m+a*g (some i))
      (standardArrayLaw (Option (Fin n))) := (integrable_const m).add ha
  rw [integral_add hai hb,
    integral_add (integrable_const m) ha, integral_const_mul, integral_const_mul,
    coordinate_mean, coordinate_mean]
  simp

lemma sharedGaussianField_covariance {n : ℕ} (m a b : ℝ) (i k : Fin n) :
    cov[fun g => sharedGaussianField m a b g i, fun g => sharedGaussianField m a b g k;
      standardArrayLaw (Option (Fin n))] = (if i=k then a^2 else 0)+b^2 := by
  have hm (i : Fin n) : MemLp (fun g : Option (Fin n) → ℝ => a*g (some i)) 2
      (standardArrayLaw (Option (Fin n))) := (coordinate_hasLaw (some i)).hasGaussianLaw.memLp_two.const_mul a
  have hb : MemLp (fun g : Option (Fin n) → ℝ => b*g none) 2
      (standardArrayLaw (Option (Fin n))) := (coordinate_hasLaw none).hasGaussianLaw.memLp_two.const_mul b
  have he (g : Option (Fin n) → ℝ) (i : Fin n) : sharedGaussianField m a b g i =
      (a*g (some i)+b*g none)+m := by unfold sharedGaussianField; ring
  have hs (j : Fin n) : Integrable (fun g : Option (Fin n) → ℝ => a*g (some j)+b*g none)
      (standardArrayLaw (Option (Fin n))) := ((hm j).add hb).integrable (by norm_num)
  simp_rw [he]
  rw [covariance_add_const_left (hs i),
    covariance_add_const_right (hs k)]
  change cov[(fun g => a*g (some i))+(fun g => b*g none),
    (fun g => a*g (some k))+(fun g => b*g none); standardArrayLaw (Option (Fin n))] = _
  rw [covariance_add_left (hm i) hb ((hm k).add hb),
    covariance_add_right (hm i) (hm k) hb,
    covariance_add_right hb (hm k) hb]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, coordinate_covariance]
  by_cases h : i=k <;> simp [h] <;> ring

lemma planted_field_representation (β : ℝ) {n : ℕ} (hn : 2 ≤ n) (x : Spin n) :
    (singleSpinPlantedLaw β x).map (gaugedField x) =
    (standardArrayLaw (Option (Fin n))).map
      (sharedGaussianField (β^2*((n:ℝ)-1)/(n:ℝ))
        (β*Real.sqrt (((n:ℝ)-2)/(n:ℝ))) (β/Real.sqrt (n:ℝ))) := by
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  apply gaussian_vector_law_ext (gaugedField_gaussian β hn0 x) (sharedGaussianField_gaussian _ _ _ _)
  · intro i
    rw [gaugedField_mean β hn0, sharedGaussianField_mean]
  · intro i k
    rw [gaugedField_covariance β hn0, sharedGaussianField_covariance]
    have ha : (β*Real.sqrt (((n:ℝ)-2)/(n:ℝ)))^2 = β^2*((n:ℝ)-2)/(n:ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hb : (β/Real.sqrt (n:ℝ))^2 = β^2/(n:ℝ) := by
      rw [div_pow, Real.sq_sqrt hnR.le]
    rw [ha,hb]
    split_ifs <;> field_simp <;> ring

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal

end

end OAI
