import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLists
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFind
import OAI.Analysis.MatrixSigning.Complexity.PolynomialSchedule
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_activeIndices : PolyTime activeIndices := by unfold activeIndices;apply poly_then
instance poly_extendEntry : PolyTime extendEntry := by unfold extendEntry;apply poly_congr
instance poly_extendVector : PolyTime extendVector := by unfold extendVector;apply poly_then
instance poly_faceView : PolyTime faceView := by unfold faceView;apply poly_reindex
instance poly_fD : PolyTime fD := by unfold fD;apply poly_then
instance poly_fRest : PolyTime fRest := by unfold fRest;apply poly_then
instance poly_fAtoms : PolyTime fAtoms := by unfold fAtoms;apply poly_then
instance poly_fArgs : PolyTime fArgs := by unfold fArgs;apply poly_then
instance poly_fBase : PolyTime fBase := by unfold fBase;apply poly_then
instance poly_fScalars : PolyTime fScalars := by unfold fScalars;apply poly_then
instance poly_fNu : PolyTime fNu := by unfold fNu;apply poly_then
instance poly_fLam : PolyTime fLam := by unfold fLam;apply poly_then
instance poly_fIndices : PolyTime fIndices := by unfold fIndices;apply poly_congr
instance poly_fN : PolyTime fN := by unfold fN;apply poly_congr
instance poly_fSchedule : PolyTime fSchedule := by unfold fSchedule;apply poly_then
instance poly_gather : PolyTime gather := by unfold gather;apply poly_mapCtx
instance poly_fState : PolyTime fState := by unfold fState;apply poly_congr
instance poly_facePointView : PolyTime facePointView := by unfold facePointView;apply poly_reindex
instance poly_fpP : PolyTime fpP := by unfold fpP;apply poly_then
instance poly_fpY : PolyTime fpY := by unfold fpY;apply poly_then
instance poly_fpExtend : PolyTime fpExtend := by unfold fpExtend;apply poly_congr
instance poly_fpPotential : PolyTime fpPotential := by unfold fpPotential;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
