import Mathlib
import OAI.Geometry.Borsuk.Support.DisjointChambers

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixCompression
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "D" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν

noncomputable def matrixCompress (e : D →ₗᵢ[ℝ] E) : Matrix ν ν ℝ →ₗ[ℝ] Matrix μ μ ℝ where
  toFun Q := (isometryMatrix e)ᴴ * Q * isometryMatrix e
  map_add' Q R := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t Q := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl

omit [DecidableEq ν] in
lemma matrixCompress_nonneg (e : D →ₗᵢ[ℝ] E) {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) :
    0 ≤ matrixCompress e Q :=
  ((Matrix.nonneg_iff_posSemidef.mp hQ).conjTranspose_mul_mul_same _).nonneg

lemma isometryMatrix_adjoint_action (e : D →ₗᵢ[ℝ] E) (x : D) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
  rw [← isometryMatrix_action e x]
  change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
    (Matrix.toEuclideanLin (isometryMatrix e))) x = x
  rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
  simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]

lemma matrixEmbed_compress (e : D →ₗᵢ[ℝ] E) {Q : Matrix ν ν ℝ}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    matrixEmbed e (matrixCompress e Q) = Q := by
  let T := isometryMatrix e
  have hleft : (T * Tᴴ) * Q = Q := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx⟩ := hR (LinearMap.mem_range_self (Matrix.toEuclideanLin Q) v)
    change e x = Matrix.toEuclideanLin Q v at hx
    rw [toEuclideanLin_mul,toEuclideanLin_mul]
    change Matrix.toEuclideanLin T (Matrix.toEuclideanLin Tᴴ (Matrix.toEuclideanLin Q v)) = _
    rw [← hx,isometryMatrix_adjoint_action,isometryMatrix_action]
  have hright : Q * (T*Tᴴ) = Q := by
    have he := congrArg Matrix.conjTranspose hleft
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at he
    simpa only [← Matrix.star_eq_conjTranspose,hQ.star_eq] using he
  change T * (Tᴴ * Q * T) * Tᴴ = Q
  calc
    _ = ((T*Tᴴ)*Q)*(T*Tᴴ) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hleft,hright]

lemma matrixCompress_trace (e : D →ₗᵢ[ℝ] E) {Q : Matrix ν ν ℝ}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    Matrix.trace (matrixCompress e Q) = Matrix.trace Q := by
  rw [← matrixEmbed_trace e,matrixEmbed_compress e hQ hR]

end MatrixCompression

end BorsukNine

end OAI
