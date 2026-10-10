import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropFibres
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropFibreGenerators

namespace OAI

section

noncomputable section
open scoped ComplexOrder CStarAlgebra

namespace CurrentMain.ProjectionRow
open ConcreteMatrixUnits

variable {I B : Type*} [Fintype I] [DecidableEq I] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] {q : B}
omit [PartialOrder B] [StarOrderedRing B] in
lemma matrixHom_unit (V : ProjectionRow I q) (i j : I) :
    V.matrixHom (unit i j)=V.entry i*star (V.entry j) := by
  change (∑ k : I,∑ l : I,(unit i j k l) • V.coeff q k l)=_
  simp only [unit,CStarMatrix.ofMatrix_apply,Matrix.single_apply,ite_and,ite_smul,one_smul,zero_smul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [coeff,V.right_support]
end CurrentMain.ProjectionRow
namespace DimensionDropRelations.Witness
open ConcreteMatrixUnits CurrentMain CompletelyPositiveOperations

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
lemma lowerEndpointHom_phi (hc : w.parameter=0) (i j : I) :
    w.lowerEndpointHom hc (unit (some i) (some j))=w.φ (matrixUnit i j) := by
  change (w.fibreRow (t := 0) (by simpa using hc) (by norm_num)).matrixHom (unit (some i) (some j))=_
  rw [ProjectionRow.matrixHom_unit]
  simpa only [fibreRow,fibreEntry,fibreColumn,sub_zero,Real.sqrt_one,inv_one,one_smul] using
    (w.zero_fibre_phi_matrix hc i j).symm
lemma lowerEndpointHom_s (hc : w.parameter=0) :
    w.lowerEndpointHom hc (unit (some p) none)=w.s := by
  let V := w.fibreRow (t := 0) (by simpa using hc) (by norm_num)
  change V.matrixHom (unit (some p) none)=w.s
  rw [ProjectionRow.matrixHom_unit]
  change V.entry (some p)*star (w.fibreAnchor 0)=w.s
  rw [w.fibreAnchor_star]
  rw [V.right_support]
  change (Real.sqrt (1-(0:ℝ)))⁻¹ • w.column p=w.s
  simpa only [sub_zero,Real.sqrt_one,inv_one,one_smul,column] using w.support
lemma upperEndpointHom_phi (hc : w.parameter=1) (i j : I) :
    w.upperEndpointHom hc (unit i j)=w.φ (matrixUnit i j) := rfl

end DimensionDropRelations.Witness

end
end

end OAI
