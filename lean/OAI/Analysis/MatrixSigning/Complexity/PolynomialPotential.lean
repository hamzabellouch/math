import Mathlib
import OAI.Analysis.MatrixSigning.Realization.PotentialRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialValueQuery

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_potentialView : PolyTime potentialView := by unfold potentialView;apply poly_reindex
instance poly_ppD : PolyTime ppD := by unfold ppD;apply poly_then
instance poly_ppRest : PolyTime ppRest := by unfold ppRest;apply poly_then
instance poly_ppAtoms : PolyTime ppAtoms := by unfold ppAtoms;apply poly_then
instance poly_ppArgs : PolyTime ppArgs := by unfold ppArgs;apply poly_then
instance poly_ppX : PolyTime ppX := by unfold ppX;apply poly_then
instance poly_ppScalars : PolyTime ppScalars := by unfold ppScalars;apply poly_then
instance poly_ppNu : PolyTime ppNu := by unfold ppNu;apply poly_then
instance poly_ppLam : PolyTime ppLam := by unfold ppLam;apply poly_then
instance poly_ppError : PolyTime ppError := by unfold ppError;apply poly_then
instance poly_ppN : PolyTime ppN := by unfold ppN;apply poly_congr
instance poly_ppRootTolerance : PolyTime ppRootTolerance := by unfold ppRootTolerance;apply poly_div
instance poly_ppTheta : PolyTime ppTheta := by unfold ppTheta;apply poly_congr
instance poly_ppQuery : PolyTime ppQuery := by unfold ppQuery;apply poly_changeOutput

def PotentialParams.scanCount (p : PotentialParams) : ℕ := p.query.scanCount
variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_potentialQuery (a : ι → PotentialParams)
    (ha : IsPoly L (fun i => (potentialCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).scanCount)) : RunsPoly L potentialQuery a := by
  unfold potentialQuery Realizes.add
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · apply RunsPoly.then_with (RunsPoly.of_poly ppQuery a ha)
    intro hw
    exact runsPoly_valueQuery_scan _ hw hn
  · exact RunsPoly.of_poly _ a ha
end CurrentKS.Realization

end

end OAI
