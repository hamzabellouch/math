import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceChoiceRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialStencil
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMemberFamily
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCurvature

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
instance poly_faP : PolyTime faP := by unfold faP;apply poly_reindex
instance poly_vectorSub : PolyTime vectorSub := by unfold vectorSub;apply poly_zipWith
instance poly_curvatureCandidates : PolyTime curvatureCandidates := by unfold curvatureCandidates;apply poly_congr
instance poly_gradientDirection : PolyTime gradientDirection := by unfold gradientDirection;apply poly_congr

lemma runsPoly_faceCurvatureParams (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) : RunsPoly L faceCurvatureParams a := by
  unfold faceCurvatureParams
  apply RunsPoly.changeOutput
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  exact (runsPoly_stencilHessian a ha hn).both (RunsPoly.of_poly _ a ha)
lemma runsPoly_faceCurvature (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) : RunsPoly L faceCurvature a :=
  (runsPoly_faceCurvatureParams a ha hn).then_poly _
lemma runsPoly_faGradientPoint (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount)) : RunsPoly L faGradientPoint a := by
  unfold faGradientPoint
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  exact runsPoly_stencilGradient _ hw hn
lemma runsPoly_faCandidates (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount)) : RunsPoly L faCandidates a := by
  unfold faCandidates
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.both (runsPoly_faGradientPoint a ha hn)
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  exact runsPoly_faceCurvature _ hw hn
lemma runsPoly_faCandidatePoints (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount)) : RunsPoly L faCandidatePoints a := by
  unfold faCandidatePoints
  apply RunsPoly.changeOutput
  exact ((RunsPoly.of_poly _ a ha).both (runsPoly_faCandidates a ha hn)).then_poly _
lemma runsPoly_scored (a : ι → FacePoint)
    (ha : IsPoly L (fun i => (facePointCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).p.scoreCount)) : RunsPoly L (fpY.both faceScore) a :=
  (RunsPoly.of_poly _ a ha).both (runsPoly_faceScore a ha hn)
lemma runsPoly_faScoredCandidates (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount))
    (hs : IsPoly L (fun i => (a i).val.scoreCount)) :
    RunsPoly L (faCandidatePoints.then (fpY.both faceScore).map) a := by
  apply RunsPoly.then_with (runsPoly_faCandidatePoints a ha hn)
  intro hw
  let xs (i : ι) := (a i).candidates.map (fun y => (⟨(a i).val,y⟩ : FacePoint))
  let b (s : Σ i,{x // x∈xs i}) : FacePoint := s.2.val
  have hb : IsPoly (fun s : Σ i,{x // x∈xs i} => L s.1) (fun s => (b s).p.scoreCount) := by
    apply (hs.reindex Sigma.fst).mono
    intro s
    obtain ⟨y,hy,he⟩ := List.mem_map.mp s.2.property
    change s.2.val.p.scoreCount≤(a s.1).val.scoreCount
    rw [←he]
  have hc := runsPoly_scored b (isPoly_listMember xs hw) hb
  apply runsPoly_map _ _ hw
  obtain ⟨p,hp⟩ := hc.cost
  exact ⟨p,fun i x hx => hp ⟨i,⟨x,hx⟩⟩⟩
lemma runsPoly_faChoice (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount))
    (hs : IsPoly L (fun i => (a i).val.scoreCount)) : RunsPoly L faChoice a := by
  unfold faChoice
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · apply RunsPoly.then_with
    · apply runsPolyOf ?_ a ha
      apply PolyTime.changeOutput
      exact poly_faP.both (poly_faP.then poly_fState)
    · intro hw
      exact runsPoly_scored _ hw hs
  · exact runsPoly_faScoredCandidates a ha hn hs
end CurrentKS.Realization

end OAI
