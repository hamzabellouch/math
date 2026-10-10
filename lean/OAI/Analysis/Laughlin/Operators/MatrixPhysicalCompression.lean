import Mathlib.Analysis.InnerProductSpace.Positive
import OAI.Analysis.Laughlin.Operators.ComplexCompression

namespace OAI

namespace Laughlin
open scoped Matrix InnerProductSpace ComplexOrder
open Matrix

theorem matrix_physical_compression {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix J I ℂ) (C : Matrix I I ℂ)
    (hC : C.IsHermitian) (hG : ((Wᴴ*W)*C*(Wᴴ*W)).PosSemidef) :
    (W*C*Wᴴ).PosSemidef := by
  have hc : (W*C*Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hC
  have hpos : ∀ x : EuclideanSpace ℂ I,
      0 ≤ (⟪x,W.toEuclideanLin.adjoint (W.toEuclideanLin
        (C.toEuclideanLin (W.toEuclideanLin.adjoint (W.toEuclideanLin x))))⟫_ℂ).re := by
    intro x
    have hp := hG.dotProduct_mulVec_nonneg (WithLp.ofLp x)
    have hp' := (Complex.nonneg_iff.mp hp).1
    simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toLpLin,Matrix.toLin'_apply,
      Matrix.mulVec_mulVec,Matrix.mul_assoc,dotProduct_comm] using hp'
  have hout := (complex_compression_positive_iff W.toEuclideanLin C.toEuclideanLin).mp hpos
  rw [← Matrix.isPositive_toEuclideanLin_iff,LinearMap.IsPositive,
    Matrix.isSymmetric_toEuclideanLin_iff]
  refine ⟨hc,?_⟩
  intro y
  have hy := hout y
  rw [inner_re_symm]
  change 0 ≤ (⟪y,(W*C*Wᴴ).toEuclideanLin y⟫_ℂ).re
  simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toLpLin,Matrix.toLin'_apply,
    Matrix.mulVec_mulVec,Matrix.mul_assoc] using hy

end Laughlin

end OAI
