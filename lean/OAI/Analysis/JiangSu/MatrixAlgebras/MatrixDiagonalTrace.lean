import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.MatrixKrausLift

namespace OAI

section

noncomputable section
namespace CompletelyPositiveOperations
open Pureness CurrentMain
open scoped ComplexOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma matrixUnit_projection (i : I) : IsStarProjection (matrixUnit i i) :=
  ⟨matrixUnit_mul i i i,matrixUnit_star i i⟩

lemma matrixUnit_diag_sum : (∑ i : I,matrixUnit i i) = (1:CStarMatrix I I ℂ) := by
  ext a b
  simp [matrix_sum_apply,matrixUnit,Matrix.single_apply,ite_and,CStarMatrix.one_apply]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
omit [StarOrderedRing B] in
theorem trace_matrix_corner (η : CStarMatrix I I ℂ →⋆ₐ[ℂ] B)
    (τ : TracialState B) (i : I) : τ.functional (η (matrixUnit i i))=(Fintype.card I : ℂ)⁻¹ := by
  let : Nonempty I := ⟨i⟩
  have hall (j : I) : τ.functional (η (matrixUnit j j))=τ.functional (η (matrixUnit i i)) := by
    rw [←matrixUnit_mul j j i,←matrixUnit_mul i i j,map_mul η,map_mul η]
    exact τ.tracial _ _
  have hs : (Fintype.card I : ℂ)*τ.functional (η (matrixUnit i i))=1 := by
    have he := congrArg (fun M => τ.functional (η M)) (matrixUnit_diag_sum (I := I))
    simpa only [map_sum, hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      map_one, τ.normalized] using he
  exact eq_inv_of_mul_eq_one_right hs

end CompletelyPositiveOperations

end
end

end OAI
