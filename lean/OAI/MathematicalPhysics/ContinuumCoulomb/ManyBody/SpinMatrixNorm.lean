import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorEffective
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Dimension-independent operator bounds for the actual spin matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary Euclidean operator represented by a finite spin matrix. -/
def spinMatrixOperator (M : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

@[simp] theorem spinMatrixOperator_apply (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    spinMatrixOperator M x i = ∑ j, M i j * x j := rfl

@[simp] theorem spinMatrixOperator_add (M N : Matrix ι ι ℂ) :
    spinMatrixOperator (M + N) = spinMatrixOperator M + spinMatrixOperator N := by
  unfold spinMatrixOperator
  rw [map_add, map_add]

@[simp] theorem spinMatrixOperator_smul (c : ℂ) (M : Matrix ι ι ℂ) :
    spinMatrixOperator (c • M) = c • spinMatrixOperator M := by
  unfold spinMatrixOperator
  rw [map_smul, map_smul]

theorem spinMatrixOperator_sum {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ) :
    spinMatrixOperator (∑ k ∈ s, M k) = ∑ k ∈ s, spinMatrixOperator (M k) := by
  unfold spinMatrixOperator
  rw [map_sum, map_sum]

@[simp] theorem spinMatrixOperator_mul (M N : Matrix ι ι ℂ) :
    spinMatrixOperator (M * N) = (spinMatrixOperator M).comp (spinMatrixOperator N) := by
  ext x i
  change Matrix.toLpLin 2 2 (M * N) x i =
    Matrix.toLpLin 2 2 M (Matrix.toLpLin 2 2 N x) i
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

@[simp] theorem spinMatrixOperator_one : spinMatrixOperator (1 : Matrix ι ι ℂ) = 1 := by
  ext x i
  simp [Matrix.one_apply]

@[simp] theorem spinMatrixOperator_star (M : Matrix ι ι ℂ) :
    spinMatrixOperator M.conjTranspose = (spinMatrixOperator M).adjoint := by
  unfold spinMatrixOperator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]

theorem spinMatrixOperator_unitary_norm_map (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) (x : EuclideanSpace ℂ ι) :
    ‖spinMatrixOperator M x‖ = ‖x‖ := by
  have hcomp : (spinMatrixOperator M).adjoint.comp (spinMatrixOperator M) = 1 := by
    rw [← spinMatrixOperator_star, ← spinMatrixOperator_mul, hM, spinMatrixOperator_one]
  have hsq : ‖spinMatrixOperator M x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hcomp]
    simp only [one_apply_eq_self, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem spinMatrixOperator_unitary_norm (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) : ‖spinMatrixOperator M‖ ≤ 1 := by
  apply (spinMatrixOperator M).opNorm_le_bound zero_le_one
  intro x
  rw [spinMatrixOperator_unitary_norm_map M hM, one_mul]

/-- Actual one-site Paulis are Hermitian. -/
theorem pauli_star (μ : Fin 3) : (pauli μ).conjTranspose = pauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

theorem sourceTensor_star (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor n M).conjTranspose = sourceTensor n (fun i => (M i).conjTranspose) := by
  ext s t
  simp only [sourceTensor, Matrix.conjTranspose_apply, star_prod]

theorem sourceLocalPauli_star (n : ℕ) (i : Fin n) (μ : Fin 3) :
    (sourceLocalPauli n i μ).conjTranspose = sourceLocalPauli n i μ := by
  unfold sourceLocalPauli
  rw [sourceTensor_star]
  congr 1
  funext k
  by_cases hki : k = i <;> simp [hki, pauli_star]

theorem sourceLocalPauli_operator_norm (n : ℕ) (i : Fin n) (μ : Fin 3) :
    ‖spinMatrixOperator (sourceLocalPauli n i μ)‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [sourceLocalPauli_star, sourceLocalPauli_sq]

theorem bellTransform_star (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (bellTransform M).conjTranspose = bellTransform M.conjTranspose := by
  unfold bellTransform
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]

theorem bellTransform_one : bellTransform 1 = 1 := by
  simp only [bellTransform, mul_one, bellMatrix_gram]

theorem firstPauli_star (μ : Fin 3) : (firstPauli μ).conjTranspose = firstPauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [firstPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply]

theorem secondPauli_star (μ : Fin 3) : (secondPauli μ).conjTranspose = secondPauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [secondPauli, pauli, twoSpinTensor, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply]

theorem bellMemberPauli_star (member : Fin 2) (μ : Fin 3) :
    (bellMemberPauli member μ).conjTranspose = bellMemberPauli member μ := by
  unfold bellMemberPauli
  split_ifs <;> rw [bellTransform_star]
  · rw [firstPauli_star]
  · rw [secondPauli_star]

theorem bellMemberPauli_sq (member : Fin 2) (μ : Fin 3) :
    bellMemberPauli member μ * bellMemberPauli member μ = 1 := by
  unfold bellMemberPauli
  split_ifs <;> rw [bellTransform_mul]
  · rw [firstPauli_sq, bellTransform_one]
  · rw [secondPauli_sq, bellTransform_one]

theorem mediatorLocal_star (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (mediatorLocal r e M).conjTranspose = mediatorLocal r e M.conjTranspose := by
  unfold mediatorLocal
  rw [mediatorTensor_star]
  congr 1
  funext f
  by_cases hfe : f = e <;> simp [hfe]

theorem mediatorLocal_one (r : ℕ) (e : Fin r) : mediatorLocal r e 1 = 1 := by
  unfold mediatorLocal
  simp only [ite_self]
  exact mediatorTensor_one r

theorem elementaryMediatorSpoke_star (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (i : Fin n) :
    (elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ)).conjTranspose =
      elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ) := by
  unfold elementaryMediatorSpoke
  rw [Matrix.conjTranspose_kronecker, sourceLocalPauli_star, mediatorLocal_star,
    bellMemberPauli_star]

theorem elementaryMediatorSpoke_sq (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (i : Fin n) :
    elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ) *
      elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ) = 1 := by
  unfold elementaryMediatorSpoke
  rw [← Matrix.mul_kronecker_mul, sourceLocalPauli_sq, mediatorLocal_mul_same,
    bellMemberPauli_sq, mediatorLocal_one, Matrix.one_kronecker_one]

theorem elementaryMediatorSpoke_operator_norm (n r : ℕ) (e : Fin r)
    (member : Fin 2) (μ : Fin 3) (i : Fin n) :
    ‖spinMatrixOperator (elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ))‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [elementaryMediatorSpoke_star, elementaryMediatorSpoke_sq]

/-- Two three-axis spokes have norm at most six, including all spectators. -/
theorem mediatorEdgeSpoke_operator_norm (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    ‖spinMatrixOperator (mediatorEdgeSpoke n r e i j member)‖ ≤ 6 := by
  unfold mediatorEdgeSpoke
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_add]
  calc
    _ ≤ ∑ μ : Fin 3, ‖spinMatrixOperator
        (elementaryMediatorSpoke n r e 0 μ (sourceLocalPauli n i μ)) +
          spinMatrixOperator (elementaryMediatorSpoke n r e member μ (sourceLocalPauli n j μ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _μ : Fin 3, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      exact ((norm_add_le _ _).trans (add_le_add
        (elementaryMediatorSpoke_operator_norm n r e 0 μ i)
        (elementaryMediatorSpoke_operator_norm n r e member μ j))).trans_eq (by norm_num)
    _ = 6 := by norm_num

/-- The actual simultaneous hopping norm is polynomial in the edge list. -/
theorem totalMediatorSpokes_operator_norm (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)‖ ≤
      6 * ∑ e, |amplitude e| := by
  unfold totalMediatorSpokes
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_smul]
  calc
    _ ≤ ∑ e, ‖(amplitude e : ℂ) • spinMatrixOperator
        (mediatorEdgeSpoke n r e (left e) (right e) (member e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, 6 * |amplitude e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (mediatorEdgeSpoke_operator_norm n r e _ _ _) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem mediatorEdgeSpoke_star (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    (mediatorEdgeSpoke n r e i j member).conjTranspose = mediatorEdgeSpoke n r e i j member := by
  unfold mediatorEdgeSpoke
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_add, elementaryMediatorSpoke_star]

theorem totalMediatorSpokes_star (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    (totalMediatorSpokes n r left right member amplitude).conjTranspose =
      totalMediatorSpokes n r left right member amplitude := by
  unfold totalMediatorSpokes
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, mediatorEdgeSpoke_star]


theorem sourceHeisenbergMatrix_star (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (sourceHeisenbergMatrix n i j).conjTranspose = sourceHeisenbergMatrix n i j := by
  simp_rw [← sourceLocalPauli_sum n i j hij]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, sourceLocalPauli_star]
  apply Finset.sum_congr rfl
  intro μ _
  exact sourceLocalPauli_commute n j i hij.symm μ μ

theorem sourceHeisenbergMatrix_operator_norm (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ‖spinMatrixOperator (sourceHeisenbergMatrix n i j)‖ ≤ 3 := by
  rw [← sourceLocalPauli_sum n i j hij, spinMatrixOperator_sum]
  simp only [spinMatrixOperator_mul]
  calc
    _ ≤ ∑ μ : Fin 3, ‖(spinMatrixOperator (sourceLocalPauli n i μ)).comp
        (spinMatrixOperator (sourceLocalPauli n j μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _μ : Fin 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (sourceLocalPauli_operator_norm n i μ)
          (sourceLocalPauli_operator_norm n j μ) (norm_nonneg _) zero_le_one).trans_eq
            (one_mul _))
    _ = 3 := by norm_num

def sourceGraphMatrix (n r : ℕ) (left right : Fin r → Fin n) (J : Fin r → ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)

theorem sourceGraphMatrix_operator_norm (n r : ℕ) (left right : Fin r → Fin n)
    (hloop : ∀ e, left e ≠ right e) (J : Fin r → ℝ) :
    ‖spinMatrixOperator (sourceGraphMatrix n r left right J)‖ ≤ 3 * ∑ e, |J e| := by
  unfold sourceGraphMatrix
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_smul]
  calc
    _ ≤ ∑ e, ‖(J e : ℂ) • spinMatrixOperator
        (sourceHeisenbergMatrix n (left e) (right e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, 3 * |J e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (sourceHeisenbergMatrix_operator_norm n _ _ (hloop e)) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end ContinuumCoulomb

end

end OAI
