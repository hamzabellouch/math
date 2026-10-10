import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialArrays
import OAI.Analysis.MatrixSigning.Realization.PencilCompileRealization
import OAI.Analysis.MatrixSigning.Realization.ValueDataRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {ea : α → Word}
local instance coordinates_natLE : PolyTime natLE := by unfold natLE;infer_instance
local instance coordinates_natEq : PolyTime natEq := by unfold natEq;infer_instance
local instance coordinates_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
local instance coordinates_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
local instance coordinates_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
local instance coordinates_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
local instance coordinates_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then

instance poly_natLT : PolyTime natLT := by unfold natLT;infer_instance
instance poly_scaleMatrix {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.scaleMatrix s) := by unfold Realizes.scaleMatrix;apply poly_then
instance poly_negateMatrix : PolyTime negateMatrix := by unfold negateMatrix;infer_instance
instance poly_zeroMatrix : PolyTime zeroMatrix := by unfold zeroMatrix;infer_instance
instance poly_reEntry : PolyTime reEntry := by unfold reEntry;infer_instance
instance poly_imEntry : PolyTime imEntry := by unfold imEntry;infer_instance
instance poly_squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime (squareTabulate r) := by unfold squareTabulate;apply poly_then
instance poly_realDecode : PolyTime realDecode := by unfold realDecode;apply poly_then
instance poly_singletonList (ea : α → Word) : PolyTime (singletonList ea) := by unfold singletonList;apply poly_then
instance poly_replicateList (ea : α → Word) : PolyTime (replicateList ea) := by unfold replicateList;infer_instance
instance poly_blockScalar : PolyTime blockScalar := by unfold blockScalar;apply poly_then
instance poly_withLevel : PolyTime withLevel := by unfold withLevel;apply poly_both
instance poly_matrixSub : PolyTime matrixSub := by
  unfold matrixSub
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_zeroRect : PolyTime zeroRect := by unfold zeroRect;apply poly_then
instance poly_blockDiagonal : PolyTime blockDiagonal := by unfold blockDiagonal;apply poly_then
instance poly_basisVector : PolyTime basisVector := by unfold basisVector;apply poly_then
instance poly_pencilFromEval {f : α×List ℚ → MatrixData}
    (r : Realizes (prodCode ea vectorCode) matrixCode f) [PolyTime r] :
    PolyTime r.pencilFromEval := by
  unfold Realizes.pencilFromEval
  refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_tabulate _ _ _ _ _ _ ?_
      refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply poly_both
      · exact poly_matrixSub
instance poly_vdD : PolyTime vdD := by unfold vdD;infer_instance
instance poly_vdRest : PolyTime vdRest := by unfold vdRest;infer_instance
instance poly_vdAtoms : PolyTime vdAtoms := by unfold vdAtoms;infer_instance
instance poly_vdParams : PolyTime vdParams := by unfold vdParams;infer_instance
instance poly_vdX : PolyTime vdX := by unfold vdX;infer_instance
instance poly_vdTheta : PolyTime vdTheta := by unfold vdTheta;infer_instance
instance poly_vdEps : PolyTime vdEps := by unfold vdEps;infer_instance
instance poly_realDimension : PolyTime realDimension := by unfold realDimension;infer_instance
instance poly_valueDimension : PolyTime valueDimension := by unfold valueDimension;infer_instance
instance poly_coordinateIndexRealizes (b : Bool) : PolyTime (coordinateIndexRealizes b) := by unfold coordinateIndexRealizes;first | infer_instance | apply poly_then
instance poly_coordinateEntry (b : Bool) : PolyTime (coordinateEntry b) := by unfold coordinateEntry;infer_instance
instance poly_coordinates (b : Bool) : PolyTime (coordinates b) := by unfold coordinates;first | infer_instance | apply poly_then
instance poly_matrixVariable (b : Bool) : PolyTime (matrixVariable b) := by unfold matrixVariable;first | infer_instance | apply poly_then

end CurrentKS.Realization

end

end OAI
