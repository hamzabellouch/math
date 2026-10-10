import Mathlib
import OAI.Analysis.AffineBernstein.ParametricChangeOfCoordinates
import OAI.Analysis.AffineBernstein.MatrixMetric

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Covector contraction with the inverse second form is unchanged by an
invertible coordinate change. This uses the actual matrix inverse. -/
lemma inverseMatrixPair_congruence (A J : Matrix ι ι ℝ) (hJ : J.det ≠ 0)
    (v w : ι → ℝ) :
    inverseMatrixPair (J.transpose*A*J) (J.transpose.mulVec v) (J.transpose.mulVec w) =
      inverseMatrixPair A v w := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have ht : IsUnit J.transpose.det := by simpa using hu
  rw [inverseMatrixPair_eq_dot,inverseMatrixPair_eq_dot,
    Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  have hv : J.transpose⁻¹.mulVec (J.transpose.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ ht,Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec,hv]
  rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]

lemma inverseMatrixPair_smul_matrix (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    (t : ℝ) (ht : t ≠ 0) (v w : ι → ℝ) :
    inverseMatrixPair (t • A) v w = t⁻¹ * inverseMatrixPair A v w := by
  let : Invertible t := invertibleOfNonzero ht
  unfold inverseMatrixPair
  rw [Matrix.inv_smul A t (isUnit_iff_ne_zero.mpr hA),invOf_eq_inv]
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma inverseMatrixPair_block_base {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) (hA : A.det ≠ 0) (hD : D.det ≠ 0)
    (v w : ι → ℝ) :
    inverseMatrixPair (Matrix.fromBlocks A 0 0 D) (Sum.elim v 0) (Sum.elim w 0) =
      inverseMatrixPair A v w := by
  have hi : (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hD),Matrix.fromBlocks_one]
  unfold inverseMatrixPair
  rw [hi]
  simp [Fintype.sum_sum_type,Matrix.fromBlocks]

/- Inverse metric of an actual parametrization and an actual test function. -/
def parametricInverseMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (X : Space n → E) (ν : E →L[ℝ] ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  inverseMatrixPair (parametricSecondForm X ν x)
    (fun i => dirDeriv (coordinateVector n i) f x)
    (fun i => dirDeriv (coordinateVector n i) f x)

lemma derivative_coordinates_comp {n : ℕ} {f : Space n → ℝ} {φ : Space n → Space n}
    {x : Space n} (hf : DifferentiableAt ℝ f (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    (fun i => dirDeriv (coordinateVector n i) (f ∘ φ) x) =
      (parametricJacobian φ x).transpose.mulVec
        (fun i => dirDeriv (coordinateVector n i) f (φ x)) := by
  funext i
  unfold dirDeriv
  rw [fderiv_comp x hf hφ]
  change fderiv ℝ f (φ x) (fderiv ℝ φ x (coordinateVector n i)) = _
  rw [← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n i))]
  simp [map_sum,map_smul,Matrix.mulVec,dotProduct,parametricJacobian]

/- Exact coordinate invariance of the inverse second-form norm. -/
lemma parametricInverseMetric_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Space n → E} {φ : Space n → Space n} {f : Space n → ℝ}
    {x : Space n} (hX : ContDiffAt ℝ ∞ X (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (hf : DifferentiableAt ℝ f (φ x)) (ν : E →L[ℝ] ℝ)
    (hν : ν.comp (fderiv ℝ X (φ x)) = 0) (hJ : (parametricJacobian φ x).det ≠ 0) :
    parametricInverseMetric (X ∘ φ) ν (f ∘ φ) x = parametricInverseMetric X ν f (φ x) := by
  unfold parametricInverseMetric
  rw [parametricSecondForm_comp hX hφ ν hν,
    derivative_coordinates_comp hf (hφ.differentiableAt (by simp))]
  exact inverseMatrixPair_congruence _ _ hJ _ _

end AffineBernstein
end

end OAI
