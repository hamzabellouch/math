import Mathlib
import OAI.Probability.SKGap.Localization.StandardArrayLaw

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
namespace SKGapCutoff.Regression

lemma clm_pi_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  conv_lhs => rw [← LinearMap.sum_single_apply (fun _ : ι => ℝ) v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext j
    by_cases h : i = j <;> simp [h]
  rw [he, map_smul]
  simp only [smul_eq_mul, mul_comm]

lemma gaussian_mean_linear {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ}
    (hX : HasGaussianLaw X μ) (L : (ι → ℝ) →L[ℝ] ℝ) :
    (∫ ω, L (X ω) ∂μ) = ∑ i, L (Pi.single i 1) * ∫ ω, X ω i ∂μ := by
  have he : (fun ω => L (X ω)) = (fun ω => ∑ i, L (Pi.single i 1) * X ω i) :=
    funext fun ω => clm_pi_expansion L (X ω)
  rw [he]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · exact fun i _ => (hX.eval i).integrable.const_mul _

lemma gaussian_variance_linear {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ}
    (hX : HasGaussianLaw X μ) (L : (ι → ℝ) →L[ℝ] ℝ) :
    Var[fun ω => L (X ω); μ] =
      ∑ i, ∑ j, L (Pi.single i 1) * L (Pi.single j 1) *
        cov[fun ω => X ω i, fun ω => X ω j; μ] := by
  let := hX.isProbabilityMeasure
  rw [← covariance_self (hX.map_fun L).aemeasurable]
  have he : (fun ω => L (X ω)) = (fun ω => ∑ i, L (Pi.single i 1) * X ω i) :=
    funext fun ω => clm_pi_expansion L (X ω)
  rw [he]
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact fun i => (hX.eval i).memLp_two.const_mul _
  · exact fun i => (hX.eval i).memLp_two.const_mul _

lemma gaussian_vector_law_ext {ι Ω Ω' : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y ν)
    (hm : ∀ i, (∫ ω, X ω i ∂μ) = ∫ ω, Y ω i ∂ν)
    (hc : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; μ] =
      cov[fun ω => Y ω i, fun ω => Y ω j; ν]) : μ.map X = ν.map Y := by
  let := hX.isGaussian_map
  let := hY.isGaussian_map
  apply Measure.ext_of_charFunDual
  funext L
  rw [hX.charFunDual_map_eq_fun L, hY.charFunDual_map_eq_fun L,
    gaussian_mean_linear hX L, gaussian_mean_linear hY L,
    gaussian_variance_linear hX L, gaussian_variance_linear hY L]
  simp_rw [hm, hc]

lemma coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ g : ι → ℝ, g i ∂standardArrayLaw ι) = 0 := by
  rw [(coordinate_hasLaw i).integral_eq, integral_id_gaussianReal]

lemma goe_entry_mean {n : ℕ} (i j : Fin n) :
    (∫ g : (Fin n × Fin n) → ℝ, goe g i j ∂standardArrayLaw (Fin n × Fin n)) = 0 := by
  simp only [goe, integral_div]
  rw [integral_add (coordinate_hasLaw (i,j)).hasGaussianLaw.integrable
    (coordinate_hasLaw (j,i)).hasGaussianLaw.integrable]
  simp only [coordinate_mean, add_zero, zero_div]

lemma sandwich_entry_mean {n r s : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (B : Matrix (Fin n) (Fin s) ℝ)
    (i : Fin r) (j : Fin s) :
    (∫ g : (Fin n × Fin n) → ℝ, (A * goe g * B) i j
      ∂standardArrayLaw (Fin n × Fin n)) = 0 := by
  have hterm (k l : Fin n) : Integrable (fun g : (Fin n × Fin n) → ℝ =>
      A i l * goe g l k * B k j) (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp l k).integrable (by norm_num)).const_mul _ |>.mul_const _
  have he (g : (Fin n × Fin n) → ℝ) : (A * goe g * B) i j =
      ∑ k, ∑ l, A i l * goe g l k * B k j := by
    simp [Matrix.mul_apply, Finset.sum_mul]
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ (fun l _ => hterm k l))]
  have inner (k : Fin n) : (∫ g : (Fin n × Fin n) → ℝ,
      ∑ l, A i l * goe g l k * B k j ∂standardArrayLaw (Fin n × Fin n)) = 0 := by
    rw [integral_finsetSum Finset.univ (fun l _ => hterm k l)]
    simp only [integral_mul_const, integral_const_mul, goe_entry_mean, mul_zero,
      zero_mul, Finset.sum_const_zero]
  simp only [inner, Finset.sum_const_zero]

def queryColumn {n : ℕ} (q : Fin n → ℝ) : Matrix (Fin n) (Fin 1) ℝ := fun i _ => q i

def queryComplement {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) :=
  P - queryColumn q * (queryColumn q)ᵀ

lemma queryColumn_unit {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) :
    (queryColumn q)ᵀ * queryColumn q = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  simpa [Matrix.mul_apply, queryColumn, pow_two] using hq

lemma queryComplement_symmetric {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = P) (q : Fin n → ℝ) : (queryComplement P q)ᵀ = queryComplement P q := by
  simp [queryComplement, hP]

lemma queryComplement_mul_column {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q) :
    queryComplement P q * queryColumn q = 0 := by
  simp [queryComplement, Matrix.sub_mul, Matrix.mul_assoc, queryColumn_unit q hq, hPq]

lemma queryComplement_sq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = P) (hPP : P*P = P) (q : Fin n → ℝ)
    (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q) :
    queryComplement P q * queryComplement P q = queryComplement P q := by
  have hqP : (queryColumn q)ᵀ * P = (queryColumn q)ᵀ := by
    simpa [Matrix.transpose_mul, hP] using congrArg Matrix.transpose hPq
  simp only [queryComplement, Matrix.sub_mul, Matrix.mul_sub]
  rw [hPP, ← Matrix.mul_assoc P, hPq, Matrix.mul_assoc _ _ P, hqP]
  rw [Matrix.mul_assoc (queryColumn q), ← Matrix.mul_assoc (queryColumn q)ᵀ,
    queryColumn_unit q hq, Matrix.one_mul]
  abel

noncomputable def queryInnovation {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n ⊕ Unit) → ℝ) (i : Fin n) : ℝ :=
  (∑ k, queryComplement P q i k * g (Sum.inl k) +
    Real.sqrt 2 * q i * g (Sum.inr ())) / Real.sqrt n

noncomputable def queryInnovationCoefficient {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (i : Fin n) : (Fin n ⊕ Unit) → ℝ :=
  Sum.elim (fun k => queryComplement P q i k / Real.sqrt n)
    (fun _ => Real.sqrt 2 * q i / Real.sqrt n)

lemma queryInnovation_as_linearTest {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n ⊕ Unit) → ℝ) (i : Fin n) :
    queryInnovation P q g i = linearTest (queryInnovationCoefficient P q i) g := by
  simp [queryInnovation, queryInnovationCoefficient, Fintype.sum_sum_type,
    add_div, ← Finset.sum_div, div_mul_eq_mul_div]

lemma queryInnovation_gaussian {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) :
    HasGaussianLaw (queryInnovation P q) (standardArrayLaw (Fin n ⊕ Unit)) := by
  have h := coordinates_gaussian.map_fun (ContinuousLinearMap.pi fun i =>
    linearTest (queryInnovationCoefficient P q i))
  apply h.congr
  filter_upwards [] with g
  funext i
  exact (queryInnovation_as_linearTest P q g i).symm

lemma queryInnovation_mean {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (i : Fin n) :
    (∫ g, queryInnovation P q g i ∂standardArrayLaw (Fin n ⊕ Unit)) = 0 := by
  simp_rw [queryInnovation_as_linearTest]
  rw [gaussian_mean_linear coordinates_gaussian]
  simp only [coordinate_mean, mul_zero, Finset.sum_const_zero]

lemma queryInnovation_covariance {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hPP : P*P = P)
    (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q)
    (i j : Fin n) :
    cov[fun g => queryInnovation P q g i, fun g => queryInnovation P q g j;
      standardArrayLaw (Fin n ⊕ Unit)] = (P i j + q i * q j) / n := by
  simp_rw [queryInnovation_as_linearTest, linearTest_apply]
  rw [linearTest_covariance]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have htwo : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hR : ∑ k, queryComplement P q i k * queryComplement P q j k =
      P i j - q i * q j := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
      (queryComplement_sq P hP hPP q hq hPq)
    have hs := queryComplement_symmetric P hP q
    have hs' (k : Fin n) : queryComplement P q k j = queryComplement P q j k :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j k) hs
    simp only [Matrix.mul_apply] at he
    have he' : (∑ k, queryComplement P q i k * queryComplement P q j k) =
        queryComplement P q i j := by
      calc
        _ = ∑ k, queryComplement P q i k * queryComplement P q k j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hs' k]
        _ = _ := he
    simpa only [queryComplement, Matrix.sub_apply,
      queryColumn, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one] using he'
  simp only [Fintype.sum_sum_type, queryInnovationCoefficient, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_unique]
  simp only [div_mul_div_comm, ← pow_two, hsq, ← Finset.sum_div]
  rw [hR]
  have ht : Real.sqrt 2 * q i * (Real.sqrt 2 * q j) = 2 * q i * q j := by
    calc
      _ = (Real.sqrt 2)^2 * (q i * q j) := by ring
      _ = _ := by rw [htwo]; ring
  rw [ht]
  ring

noncomputable def queryAnswerCLM {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ((entryCLM i 0).comp
    (sandwichCLM P (queryColumn q))).comp (goeCLM n)

lemma queryAnswerCLM_apply {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n × Fin n) → ℝ) :
    queryAnswerCLM P q g = fun i => (P * goe g * queryColumn q) i 0 := by
  simp [queryAnswerCLM]

lemma queryAnswer_covariance {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hPP : P*P = P)
    (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q)
    (i j : Fin n) :
    cov[fun g : (Fin n × Fin n) → ℝ => (P * goe g * queryColumn q) i 0,
      fun g => (P * goe g * queryColumn q) j 0; standardArrayLaw (Fin n × Fin n)] =
        (P i j + q i * q j) / n := by
  rw [goe_sandwich_covariance hn]
  simp [queryColumn_unit q hq, hP, hPP, hPq, queryColumn, mul_comm]

lemma query_innovation_law {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hPP : P*P = P)
    (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q) :
    (standardArrayLaw (Fin n × Fin n)).map
      (fun g => fun i => (P * goe g * queryColumn q) i 0) =
    (standardArrayLaw (Fin n ⊕ Unit)).map (queryInnovation P q) := by
  apply gaussian_vector_law_ext
    ((coordinates_gaussian.map_fun (queryAnswerCLM P q)).congr
      (Filter.Eventually.of_forall (queryAnswerCLM_apply P q)))
    (queryInnovation_gaussian P q)
  · intro i
    rw [sandwich_entry_mean, queryInnovation_mean]
  · intro i j
    rw [queryAnswer_covariance hn P hP hPP q hq hPq,
      queryInnovation_covariance hn P hP hPP q hq hPq]

noncomputable def freshRegressionCLM {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : ((Fin n × Fin n) → ℝ) →L[ℝ]
      (((Fin n × Fin n) → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearMap.pi fun p : Fin n × Fin n => ((entryCLM p.1 p.2).comp
    (sandwichCLM (queryComplement P q) (queryComplement P q))).comp (goeCLM n)).prod
      (queryAnswerCLM P q)

lemma freshRegressionCLM_apply {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n × Fin n) → ℝ) :
    freshRegressionCLM P q g =
      (fun p : Fin n × Fin n => (queryComplement P q * goe g * queryComplement P q) p.1 p.2,
        fun i => (P * goe g * queryColumn q) i 0) := by
  simp [freshRegressionCLM, queryAnswerCLM_apply]

lemma fresh_residual_independent {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P)
    (q : Fin n → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hPq : P * queryColumn q = queryColumn q) :
    IndepFun (fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
      (queryComplement P q * goe g * queryComplement P q) p.1 p.2)
      (fun g => fun i => (P * goe g * queryColumn q) i 0)
      (standardArrayLaw (Fin n × Fin n)) := by
  have hXY := (coordinates_gaussian.map_fun (freshRegressionCLM P q)).congr
    (Filter.Eventually.of_forall (freshRegressionCLM_apply P q))
  apply hXY.indepFun_of_covariance_eval
  intro p i
  rw [goe_sandwich_covariance hn]
  simp [queryComplement_symmetric P hP q, queryComplement_mul_column P q hq hPq]

end SKGapCutoff.Regression

open scoped BigOperators

end

end OAI
