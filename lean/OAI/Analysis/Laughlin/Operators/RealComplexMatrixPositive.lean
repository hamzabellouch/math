import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem real_complex_matrix_hermitian {I : Type*} (M : Matrix I I ℝ) (hM : M.IsHermitian) :
    (M.map Complex.ofReal).IsHermitian := by
  ext i j
  have h := congrFun (congrFun hM.eq i) j
  simpa [Matrix.conjTranspose_apply,Matrix.map_apply] using congrArg Complex.ofReal h

theorem real_complex_matrix_positive {I : Type*} [Fintype I]
    (M : Matrix I I ℝ) (hM : M.PosSemidef) : (M.map Complex.ofReal).PosSemidef := by
  have hh := real_complex_matrix_hermitian M hM.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro z
  apply Complex.nonneg_iff.mpr
  constructor
  · have hr := hM.dotProduct_mulVec_nonneg (fun i => (z i).re)
    have hi := hM.dotProduct_mulVec_nonneg (fun i => (z i).im)
    have he : (star z ⬝ᵥ ((M.map Complex.ofReal)*ᵥ z)).re =
        (star (fun i => (z i).re) ⬝ᵥ (M*ᵥ (fun i => (z i).re))) +
        (star (fun i => (z i).im) ⬝ᵥ (M*ᵥ (fun i => (z i).im))) := by
      simp [dotProduct,Matrix.mulVec,Complex.mul_re,Complex.mul_im,Complex.re_sum,
        Matrix.map_apply,
        Finset.mul_sum,Finset.sum_add_distrib,sub_eq_add_neg]
    rw [he]
    exact add_nonneg hr hi
  · exact (hh.im_star_dotProduct_mulVec_self z).symm

end Laughlin

end OAI
