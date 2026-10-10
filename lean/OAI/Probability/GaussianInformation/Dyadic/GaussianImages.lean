import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.ReplicaMoments

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

lemma finiteProduct_le {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] {μ ν : ∀ i, Measure (E i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  have ho : (OuterMeasure.pi fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi fun i => (ν i).toOuterMeasure := by
    apply OuterMeasure.le_pi.mpr
    intro t ht
    exact (OuterMeasure.pi_pi_le _ _).trans
      (Finset.prod_le_prod fun i _ => h i (t i))
  exact ho s

lemma standardGaussianPDF_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  change (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0)^2 / (2 * 1)) ≤ 1
  simp only [mul_one, sub_zero]
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hi : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have he : Real.exp (-(x^2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa using hi)

lemma standardGaussian_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  exact withDensity_mono (ae_of_all _ standardGaussianPDF_le_one)

lemma iidGaussian_le_volume (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1) ≤ (volume : Measure (ι → ℝ)) :=
  finiteProduct_le fun _ => standardGaussian_le_volume

lemma gaussian_square_map_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (Matrix.toLin' M) ≤
      ENNReal.ofReal (|M.det|⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hmap := Measure.map_mono (iidGaussian_le_volume ι)
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hM, abs_inv] at hmap
  exact hmap

open Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

lemma rectangularGaussian_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    (stdGaussian (EuclideanSpace ℝ κ)).map
      (LinearMap.toContinuousLinearMap A.toEuclideanLin) =
      multivariateGaussian 0 (A * Aᵀ) := by
  have hA : (A * Aᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian hA, innerSL_apply_apply ℝ,
      ← LinearMap.adjoint_toContinuousLinearMap,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      Matrix.conjTranspose_eq_transpose_of_trivial, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial]
    change (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A * Aᵀ) *ᵥ y
    rw [dotProduct_comm (Aᵀ *ᵥ y)]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
    simp [Matrix.dotProduct_mulVec]

lemma rectangularGaussian_squareRoot_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (Matrix.toLin' A) =
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (Matrix.toLin' (CFC.sqrt (A * Aᵀ))) := by
  have he := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) => μ.map ofLp)
    (rectangularGaussian_eq A)
  unfold multivariateGaussian at he
  simp only [zero_add] at he
  rw [← map_pi_eq_stdGaussian, ← map_pi_eq_stdGaussian] at he
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at he
  exact he

lemma gaussian_rectangular_map_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (Matrix.toLin' A) ≤
      ENNReal.ofReal ((Real.sqrt (A * Aᵀ).det)⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hpos : (A * Aᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose A
  have hd : (CFC.sqrt (A * Aᵀ)).det = Real.sqrt (A * Aᵀ).det := by
    rw [hpos.det_sqrt, RCLike.sqrt_of_nonneg hpos.det_nonneg]
    rfl
  have hD : (CFC.sqrt (A * Aᵀ)).det ≠ 0 := by
    rw [hd]
    exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hpos.det_nonneg hA.symm)
  rw [rectangularGaussian_squareRoot_eq]
  convert gaussian_square_map_le (CFC.sqrt (A * Aᵀ)) hD using 1
  rw [hd, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma gaussian_rectangular_box_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) (η : ℝ) (hη : 0 ≤ η) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1))
      {x | ∀ i, |(A *ᵥ x) i| ≤ η} ≤
      ENNReal.ofReal ((Real.sqrt (A * Aᵀ).det)⁻¹ * (2 * η) ^ Fintype.card ι) := by
  have he : {x : κ → ℝ | ∀ i, |(A *ᵥ x) i| ≤ η} =
      (Matrix.toLin' A) ⁻¹' (Set.univ.pi fun _ : ι => Set.Icc (-η) η) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_true_left, Matrix.toLin'_apply, Set.mem_Icc, abs_le]
  rw [he, ← Measure.map_apply (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
    (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc)]
  refine (gaussian_rectangular_map_le A hA _).trans_eq ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const,
    Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]

lemma gaussian_multirow_box_le {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : (A * Aᵀ).det ≠ 0) (η : ℝ) (hη : 0 ≤ η) :
    (Measure.pi (fun _ : ρ => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      {X | ∀ r i, |(A *ᵥ X r) i| ≤ η} ≤
      ENNReal.ofReal (((Real.sqrt (A * Aᵀ).det)⁻¹ * (2 * η)^Fintype.card ι)^Fintype.card ρ) := by
  have he : {X : ρ → κ → ℝ | ∀ r i, |(A *ᵥ X r) i| ≤ η} =
      Set.univ.pi (fun _ : ρ => {x : κ → ℝ | ∀ i, |(A *ᵥ x) i| ≤ η}) := by
    ext x
    simp
  rw [he, Measure.pi_pi, ENNReal.ofReal_pow (by positivity)]
  simpa using Finset.prod_le_prod (s := (Finset.univ : Finset ρ))
    (fun _ _ => gaussian_rectangular_box_le A hA η hη)

end RepeatedLocalization

namespace RepeatedLocalization
open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

lemma gaussian_multirow_box_le_extended {ρ ι κ : Type*} [Fintype ρ] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (hρ : 0 < Fintype.card ρ)
    (A : Matrix ι κ ℝ) (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : ρ => Measure.pi (fun _ : κ => gaussianReal 0 1)))
      {X | ∀ r i, |(A *ᵥ X r) i| ≤ η} ≤
      (ENNReal.ofReal (Real.sqrt (A * Aᵀ).det))⁻¹ ^ Fintype.card ρ *
        ENNReal.ofReal ((2*η)^(Fintype.card ι * Fintype.card ρ)) := by
  by_cases hA : (A * Aᵀ).det ≠ 0
  · refine (gaussian_multirow_box_le A hA η hη.le).trans_eq ?_
    have hpos : (A * Aᵀ).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose A
    have hd : 0 < Real.sqrt (A * Aᵀ).det := Real.sqrt_pos.mpr
      (lt_of_le_of_ne hpos.det_nonneg hA.symm)
    rw [mul_pow, ← pow_mul, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hd]
  · simp only [not_ne_iff] at hA
    rw [hA, Real.sqrt_zero, ENNReal.ofReal_zero, ENNReal.inv_zero,
      ENNReal.top_pow hρ.ne', ENNReal.top_mul (by positivity)]
    exact le_top

noncomputable def rowMatrix {q d : ℕ} (f : Fin q → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin q) (Fin d) ℝ := fun i j => f i j

lemma rowMatrix_gram {q d : ℕ} (f : Fin q → EuclideanSpace ℝ (Fin d)) :
    rowMatrix f * (rowMatrix f)ᵀ = Matrix.gram ℝ f := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowMatrix, Matrix.gram_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end RepeatedLocalization

end OAI
