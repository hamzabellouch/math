import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialStored
import OAI.Analysis.MatrixSigning.Realization.OriginalSignRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCoordinates

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_originalView : PolyTime originalView := by unfold originalView;apply poly_reindex
instance poly_originalD : PolyTime originalD := by unfold originalD;apply poly_then
instance poly_originalRecords : PolyTime originalRecords := by unfold originalRecords;apply poly_then
instance poly_originalN : PolyTime originalN := by unfold originalN;apply poly_congr
instance poly_recordEntry (imag : Bool) : PolyTime (recordEntry imag) := by unfold recordEntry;apply poly_then
instance poly_recordCoordinate : PolyTime recordCoordinate := by unfold recordCoordinate;apply poly_congr
instance poly_recordCoordinates : PolyTime recordCoordinates := by unfold recordCoordinates;apply poly_then
instance poly_originalRecord : PolyTime originalRecord := by unfold originalRecord;apply poly_congr
instance poly_originalCoordinates : PolyTime originalCoordinates := by unfold originalCoordinates;apply poly_congr
instance poly_recordTrace : PolyTime recordTrace := by unfold recordTrace;apply poly_then
instance poly_originalTrace : PolyTime originalTrace := by unfold originalTrace;apply poly_congr
instance poly_originalTraces : PolyTime originalTraces := by unfold originalTraces;apply poly_tabulateFin
instance poly_originalScale : PolyTime originalScale := by unfold originalScale;apply poly_congr
instance poly_originalOrientation : PolyTime originalOrientation := by unfold originalOrientation;apply poly_congr
instance poly_nonzeroIndices : PolyTime nonzeroIndices := by unfold nonzeroIndices;apply poly_congr
instance poly_originalIndices : PolyTime originalIndices := by unfold originalIndices;apply poly_congr
instance poly_originalCountRealizes : PolyTime originalCountRealizes := by unfold originalCountRealizes;apply poly_congr
instance poly_originalIndex : PolyTime originalIndex := by unfold originalIndex;apply poly_changeOutput
instance poly_originalNormalizedMatrix : PolyTime originalNormalizedMatrix := by unfold originalNormalizedMatrix;apply poly_congr
instance poly_originalFaceRealizes : PolyTime originalFaceRealizes := by unfold originalFaceRealizes;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
