import Mathlib
import OAI.Probability.SKGap.Model

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
namespace SKGapCutoff.Regression

local instance matrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

local instance matrixBorel {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))

noncomputable def standardArrayLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance {ι : Type*} [Fintype ι] : IsProbabilityMeasure (standardArrayLaw ι) := by
  unfold standardArrayLaw
  infer_instance

lemma coordinate_hasLaw {ι : Type*} [Fintype ι] (i : ι) :
    HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1) (standardArrayLaw ι) :=
  (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw

lemma coordinates_independent {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (g : ι → ℝ) => g i) (standardArrayLaw ι) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma coordinates_gaussian {ι : Type*} [Fintype ι] :
    HasGaussianLaw (fun g : ι → ℝ => g) (standardArrayLaw ι) :=
  coordinates_independent.hasGaussianLaw (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun g : ι → ℝ => g i, fun g => g j; standardArrayLaw ι] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (coordinate_hasLaw i).aemeasurable,
      (coordinate_hasLaw i).variance_eq, variance_id_gaussianReal]
    simp
  · rw [ite_eq_right h]
    exact (coordinates_independent.indepFun h).covariance_eq_zero
      ((coordinate_hasLaw i).hasGaussianLaw.memLp_two)
      ((coordinate_hasLaw j).hasGaussianLaw.memLp_two)

noncomputable def linearTest {ι : Type*} [Fintype ι] (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

@[simp] lemma linearTest_apply {ι : Type*} [Fintype ι] (a g : ι → ℝ) :
    linearTest a g = ∑ i, a i * g i := by simp [linearTest]

lemma linearTest_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) :
    cov[fun g : ι → ℝ => ∑ i, a i * g i,
      fun g => ∑ i, b i * g i; standardArrayLaw ι] = ∑ i, a i * b i := by
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right, coordinate_covariance]
    simp
  · exact fun i => ((coordinate_hasLaw i).hasGaussianLaw.memLp_two).const_mul _
  · exact fun i => ((coordinate_hasLaw i).hasGaussianLaw.memLp_two).const_mul _

noncomputable def goe {n : ℕ} (g : (Fin n × Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (g (i,j) + g (j,i)) / Real.sqrt (2*n)

lemma goe_symmetric {n : ℕ} (g : (Fin n × Fin n) → ℝ) : (goe g)ᵀ = goe g := by
  ext i j
  simp [goe, add_comm]

noncomputable def goeCLM (n : ℕ) : ((Fin n × Fin n) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (Real.sqrt (2*n))⁻¹ • ((ContinuousLinearMap.proj (i,j) : ((Fin n × Fin n) → ℝ) →L[ℝ] ℝ) + ContinuousLinearMap.proj (j,i))

@[simp] lemma goeCLM_apply (n : ℕ) (g : (Fin n × Fin n) → ℝ) : goeCLM n g = goe g := by
  ext i j
  change (Real.sqrt (2*n))⁻¹ * (g (i,j) + g (j,i)) =
    (g (i,j) + g (j,i)) / Real.sqrt (2*n)
  rw [div_eq_mul_inv, mul_comm]

lemma goe_gaussian (n : ℕ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => goe g)
      (standardArrayLaw (Fin n × Fin n)) := by
  have h := coordinates_gaussian.map_fun
    (show ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) from goeCLM n)
  exact h.congr (Filter.Eventually.of_forall (goeCLM_apply n))

lemma goe_entry_memLp {n : ℕ} (i j : Fin n) :
    MemLp (fun g : (Fin n × Fin n) → ℝ => goe g i j) 2 (standardArrayLaw (Fin n × Fin n)) :=
  ((goe_gaussian n).eval i |>.eval j).memLp_two

lemma goe_entry_covariance {n : ℕ} (hn : 0 < n) (i j k l : Fin n) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j, fun g => goe g k l;
        standardArrayLaw (Fin n × Fin n)] =
      ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) / n := by
  have hLp (a : Fin n × Fin n) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  simp only [goe, covariance_fun_div_left, covariance_fun_div_right]
  change cov[(fun g => g (i,j)) + (fun g => g (j,i)),
    (fun g => g (k,l)) + (fun g => g (l,k)); standardArrayLaw (Fin n × Fin n)] /
      Real.sqrt (2*n) / Real.sqrt (2*n) = _
  rw [covariance_add_left (hLp _) (hLp _) ((hLp _).add (hLp _)),
    covariance_add_right (hLp _) (hLp _) (hLp _),
    covariance_add_right (hLp _) (hLp _) (hLp _)]
  simp only [coordinate_covariance, Prod.mk.injEq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (2*n) ^ 2 = 2*n := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2*(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [div_div, ← pow_two]
  rw [hs]
  have ha : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have hb : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [ha, hb]
  ring

noncomputable def sandwichCLM {a n b : ℕ}
    (A : Matrix (Fin a) (Fin n) ℝ) (B : Matrix (Fin n) (Fin b) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin a) (Fin b) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun G => A * G * B
    map_add' := by intro G H; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intro c G; simp [Matrix.mul_smul, Matrix.smul_mul] }

@[simp] lemma sandwichCLM_apply {a n b : ℕ}
    (A : Matrix (Fin a) (Fin n) ℝ) (B : Matrix (Fin n) (Fin b) ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) : sandwichCLM A B G = A * G * B := rfl

def residualProjection {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - U * Uᵀ

lemma residualProjection_symmetric {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) :
    (residualProjection U)ᵀ = residualProjection U := by
  simp [residualProjection]

lemma residualProjection_mul {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    residualProjection U * U = 0 := by
  simp [residualProjection, Matrix.sub_mul, Matrix.mul_assoc, hU]

lemma mul_residualProjection {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    Uᵀ * residualProjection U = 0 := by
  simp [residualProjection, Matrix.mul_sub, ← Matrix.mul_assoc, hU]

lemma regression_decomposition {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ) (hG : Gᵀ = G) :
    G = (G*U)*Uᵀ + U*(G*U)ᵀ - U*(Uᵀ*(G*U))*Uᵀ +
      residualProjection U * G * residualProjection U := by
  simp only [Matrix.transpose_mul, hG, residualProjection]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.mul_assoc]
  abel

lemma goe_entry_sandwich_covariance {n a b : ℕ} (hn : 0 < n)
    (C : Matrix (Fin a) (Fin n) ℝ) (D : Matrix (Fin n) (Fin b) ℝ)
    (i j : Fin n) (k : Fin a) (l : Fin b) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j,
        fun g => (C * goe g * D) k l; standardArrayLaw (Fin n × Fin n)] =
      (C k i * D j l + C k j * D i l) / n := by
  have hterm (p q : Fin n) : MemLp (fun g : (Fin n × Fin n) → ℝ =>
      C k q * goe g q p * D p l) 2 (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp q p).const_mul _).mul_const _
  have hsum (p : Fin n) := memLp_finsetSum Finset.univ (fun q _ => hterm p q)
  have he (g : (Fin n × Fin n) → ℝ) : (C * goe g * D) k l =
      ∑ p, ∑ q, C k q * goe g q p * D p l := by
    simp [Matrix.mul_apply, Finset.sum_mul]
  simp_rw [he]
  rw [covariance_fun_sum_right hsum (goe_entry_memLp i j)]
  simp_rw [covariance_fun_sum_right (fun q => hterm _ q) (goe_entry_memLp i j),
    covariance_mul_const_right, covariance_const_mul_right, goe_entry_covariance hn]
  simp only [ite_and, add_div, mul_add, add_mul, Finset.sum_add_distrib,
    ite_div, mul_ite, ite_mul, zero_div, mul_zero, zero_mul]
  simp
  ring

lemma goe_sandwich_covariance {n a b c d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin a) (Fin n) ℝ) (B : Matrix (Fin n) (Fin b) ℝ)
    (C : Matrix (Fin c) (Fin n) ℝ) (D : Matrix (Fin n) (Fin d) ℝ)
    (i : Fin a) (j : Fin b) (k : Fin c) (l : Fin d) :
    cov[fun g : (Fin n × Fin n) → ℝ => (A * goe g * B) i j,
        fun g => (C * goe g * D) k l; standardArrayLaw (Fin n × Fin n)] =
      ((Bᵀ * D) j l * (A * Cᵀ) i k + (C * B) k j * (A * D) i l) / n := by
  have hterm (p q : Fin n) : MemLp (fun g : (Fin n × Fin n) → ℝ =>
      A i q * goe g q p * B p j) 2 (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp q p).const_mul _).mul_const _
  have hsum (p : Fin n) := memLp_finsetSum Finset.univ (fun q _ => hterm p q)
  have hCD : MemLp (fun g : (Fin n × Fin n) → ℝ => (C * goe g * D) k l)
      2 (standardArrayLaw (Fin n × Fin n)) := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact memLp_finsetSum _ (fun p _ => memLp_finsetSum _
      (fun q _ => ((goe_entry_memLp q p).const_mul _).mul_const _))
  have he (g : (Fin n × Fin n) → ℝ) : (A * goe g * B) i j =
      ∑ p, ∑ q, A i q * goe g q p * B p j := by
    simp [Matrix.mul_apply, Finset.sum_mul]
  simp_rw [he]
  rw [covariance_fun_sum_left hsum hCD]
  simp_rw [covariance_fun_sum_left (fun q => hterm _ q) hCD,
    covariance_mul_const_left, covariance_const_mul_left, goe_entry_sandwich_covariance hn]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← mul_div_assoc, div_mul_eq_mul_div, ← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / n)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma residual_answer_covariance {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (i j k : Fin n) (l : Fin r) :
    cov[fun g : (Fin n × Fin n) → ℝ =>
        (residualProjection U * goe g * residualProjection U) i j,
      fun g => (goe g * U) k l; standardArrayLaw (Fin n × Fin n)] = 0 := by
  have h := goe_sandwich_covariance hn (residualProjection U) (residualProjection U)
    (1 : Matrix (Fin n) (Fin n) ℝ) U i j k l
  simpa [residualProjection_symmetric, residualProjection_mul U hU] using h

noncomputable def entryCLM {n m : ℕ} (i : Fin n) (j : Fin m) :
    Matrix (Fin n) (Fin m) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin n → Fin m → ℝ) →L[ℝ] (Fin m → ℝ))

@[simp] lemma entryCLM_apply {n m : ℕ} (i : Fin n) (j : Fin m)
    (G : Matrix (Fin n) (Fin m) ℝ) : entryCLM i j G = G i j := rfl

noncomputable def regressionCLM {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) :
    ((Fin n × Fin n) → ℝ) →L[ℝ]
      (((Fin n × Fin n) → ℝ) × ((Fin n × Fin r) → ℝ)) :=
  (ContinuousLinearMap.pi (fun p : Fin n × Fin n =>
    ((entryCLM p.1 p.2).comp (sandwichCLM (residualProjection U) (residualProjection U))).comp
      (goeCLM n))).prod
    (ContinuousLinearMap.pi (fun p : Fin n × Fin r =>
      ((entryCLM p.1 p.2).comp (sandwichCLM (1 : Matrix (Fin n) (Fin n) ℝ) U)).comp
        (goeCLM n)))

lemma regressionCLM_apply {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (g : (Fin n × Fin n) → ℝ) :
    regressionCLM U g =
      (fun p : Fin n × Fin n => (residualProjection U * goe g * residualProjection U) p.1 p.2,
       fun p : Fin n × Fin r => (goe g * U) p.1 p.2) := by
  change (fun p : Fin n × Fin n =>
      (residualProjection U * (goeCLM n) g * residualProjection U) p.1 p.2,
    fun p : Fin n × Fin r => ((1 : Matrix (Fin n) (Fin n) ℝ) * (goeCLM n) g * U) p.1 p.2) = _
  rw [goeCLM_apply, Matrix.one_mul]

lemma residual_answer_independent {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    IndepFun (fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
      (residualProjection U * goe g * residualProjection U) p.1 p.2)
      (fun g => fun p : Fin n × Fin r => (goe g * U) p.1 p.2)
      (standardArrayLaw (Fin n × Fin n)) := by
  have hXY := (coordinates_gaussian.map_fun (regressionCLM U)).congr
    (Filter.Eventually.of_forall (regressionCLM_apply U))
  exact hXY.indepFun_of_covariance_eval (fun p q =>
    residual_answer_covariance hn U hU p.1 p.2 q.1 q.2)

def revealedCompletion {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Y * Uᵀ + U * Yᵀ - U * (Uᵀ * Y) * Uᵀ

lemma revealedCompletion_answer {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (hY : Uᵀ * Y = Yᵀ * U) :
    revealedCompletion U Y * U = Y := by
  simp only [revealedCompletion, Matrix.sub_mul, Matrix.add_mul]
  rw [Matrix.mul_assoc Y, hU, Matrix.mul_one, Matrix.mul_assoc U Yᵀ,
    Matrix.mul_assoc (U * (Uᵀ * Y)), hU, Matrix.mul_one, hY]
  abel

lemma revealedCompletion_symmetric {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (hY : Uᵀ * Y = Yᵀ * U) :
    (revealedCompletion U Y)ᵀ = revealedCompletion U Y := by
  simp only [revealedCompletion, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← hY]
  simp only [Matrix.mul_assoc]
  abel

lemma revealedCompletion_residual {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) :
    residualProjection U * revealedCompletion U Y * residualProjection U = 0 := by
  simp only [revealedCompletion, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul,
    Matrix.add_mul]
  rw [Matrix.mul_assoc (residualProjection U) (Y * Uᵀ) (residualProjection U)]
  rw [Matrix.mul_assoc Y Uᵀ (residualProjection U), mul_residualProjection U hU,
    Matrix.mul_zero, Matrix.mul_zero]
  simp only [← Matrix.mul_assoc, residualProjection_mul U hU, Matrix.zero_mul,
    add_zero, sub_zero]

lemma revealedCompletion_unique {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (U Y : Matrix (Fin n) (Fin r) ℝ) (hG : Gᵀ = G) (hY : G*U = Y)
    (hR : residualProjection U * G * residualProjection U = 0) :
    G = revealedCompletion U Y := by
  simpa only [hY, hR, add_zero, revealedCompletion] using regression_decomposition G U hG

lemma regression_factorization {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    (standardArrayLaw (Fin n × Fin n)).map (fun g =>
      (fun p : Fin n × Fin n => (residualProjection U * goe g * residualProjection U) p.1 p.2,
       fun p : Fin n × Fin r => (goe g * U) p.1 p.2)) =
      ((standardArrayLaw (Fin n × Fin n)).map (fun g => fun p : Fin n × Fin n =>
        (residualProjection U * goe g * residualProjection U) p.1 p.2)).prod
      ((standardArrayLaw (Fin n × Fin n)).map (fun g => fun p : Fin n × Fin r =>
        (goe g * U) p.1 p.2)) := by
  have hXY := (coordinates_gaussian.map_fun (regressionCLM U)).congr
    (Filter.Eventually.of_forall (regressionCLM_apply U))
  exact (residual_answer_independent hn U hU).map_prod_eq_prod_map_map
    hXY.fst.aemeasurable hXY.snd.aemeasurable

end SKGapCutoff.Regression

open scoped BigOperators

end

end OAI
