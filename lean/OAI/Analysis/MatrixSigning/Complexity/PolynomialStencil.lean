import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialArrays
import OAI.Analysis.MatrixSigning.Complexity.PolynomialSchedule
import OAI.Analysis.MatrixSigning.Realization.StencilRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceBasics
import OAI.Analysis.MatrixSigning.Complexity.PolynomialExplicit
import OAI.Analysis.MatrixSigning.Complexity.PolynomialArithmeticFamilies
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceQuery
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFinFamilies
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCurvature

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
instance poly_fiP : PolyTime fiP := by unfold fiP;apply poly_familyFirst
instance poly_fiI : PolyTime fiI := by unfold fiI;apply poly_familyIndex
instance poly_fiBasis : PolyTime fiBasis := by unfold fiBasis;apply poly_congr
instance poly_fdS : PolyTime fdS := by unfold fdS;apply poly_familyFirst
instance poly_fdP : PolyTime fdP := by unfold fdP;apply poly_then
instance poly_fdI : PolyTime fdI := by unfold fdI;apply poly_then
instance poly_fdJ : PolyTime fdJ := by unfold fdJ;apply poly_familyIndex
instance poly_fdBasisI : PolyTime fdBasisI := by unfold fdBasisI;apply poly_then
instance poly_fdBasisJ : PolyTime fdBasisJ := by unfold fdBasisJ;apply poly_congr

lemma runsPoly_stencilAt {ea : α → Word} (p : α → FaceParams) (pr : Realizes ea faceCode p)
    [PolyTime pr] (v : (a : α) → Fin (p a).n → ℚ)
    (vr : Realizes ea vectorCode (fun a => List.ofFn (v a))) [PolyTime vr]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hn : IsPoly L (fun i => (p (a i)).stencilCount)) :
    RunsPoly L (stencilAt p pr v vr) a := by
  unfold stencilAt
  apply RunsPoly.then_with
  · apply runsPolyOf ?_ a ha
    apply PolyTime.changeOutput
    apply PolyTime.both ‹PolyTime pr›
    apply PolyTime.then ?_ poly_vectorAdd
    apply PolyTime.both (PolyTime.then ‹PolyTime pr› poly_fState)
    exact ((((‹PolyTime pr›).then poly_fSchedule).then (poly_parameterField 5)).both ‹PolyTime vr›).then poly_vectorScale
  · intro hw
    exact runsPoly_faceStencil _ hw hn

lemma runsPoly_stencilGradientEntry (a : ι → FaceIndex)
    (ha : IsPoly L (fun i => (faceIndexCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.stencilCount)) :
    RunsPoly L stencilGradientEntry a := by
  unfold stencilGradientEntry
  apply RunsPoly.div
  · apply RunsPoly.sub
    · exact runsPoly_stencilAt _ _ _ _ a ha hn
    · exact runsPoly_stencilAt _ _ _ _ a ha hn
  · exact runsPolyOf ((poly_constant _ _ 2).mul ((poly_fiP.then poly_fSchedule).then (poly_parameterField 5))) a ha

lemma runsPoly_stencilGradient (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) :
    RunsPoly L stencilGradient a := by
  unfold stencilGradient
  apply runsPoly_tabulateFin_family _ _ a ha
  exact runsPoly_stencilGradientEntry (fun s : Σ i,Fin (a i).n => ⟨a s.1,s.2⟩)
    (isPoly_finFamily fN a ha) (hn.reindex Sigma.fst)

lemma runsPoly_stencilHessianEntry (a : ι → FaceDouble)
    (ha : IsPoly L (fun i => (faceDoubleCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.1.stencilCount)) :
    RunsPoly L stencilHessianEntry a := by
  unfold stencilHessianEntry
  dsimp only
  apply RunsPoly.congr
  apply RunsPoly.ite (RunsPoly.of_poly _ a ha)
  · apply RunsPoly.div
    · apply RunsPoly.add
      · apply RunsPoly.sub
        · exact runsPoly_stencilAt _ _ _ _ a ha hn
        · apply RunsPoly.mul (RunsPoly.of_poly _ a ha)
          apply RunsPoly.then_with
          · apply runsPolyOf ?_ a ha
            apply PolyTime.changeOutput
            exact poly_fdP.both (poly_fdP.then poly_fState)
          · intro hw
            exact runsPoly_faceStencil _ hw hn
      · exact runsPoly_stencilAt _ _ _ _ a ha hn
    · exact runsPolyOf (((poly_fdP.then poly_fSchedule).then (poly_parameterField 5)).pow 2) a ha
  · apply RunsPoly.div
    · apply RunsPoly.add
      · apply RunsPoly.sub
        · apply RunsPoly.sub
          · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
              (((poly_fdBasisI.both poly_fdBasisJ).then poly_vectorAdd).congr
                (fun _ => vectorAdd_ofFn _ _)) a ha hn
          · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
              (((poly_fdBasisI.both ((poly_fdBasisJ.then poly_vectorNeg).congr
                (fun _ => vectorNeg_ofFn _))).then poly_vectorAdd).congr
                (fun _ => vectorAdd_ofFn _ _)) a ha hn
        · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
            (((((poly_fdBasisI.then poly_vectorNeg).congr (fun _ => vectorNeg_ofFn _)).both
              poly_fdBasisJ).then poly_vectorAdd).congr (fun _ => vectorAdd_ofFn _ _)) a ha hn
      · exact @runsPoly_stencilAt _ _ _ _ _ _ poly_fdP _ _
          (((((poly_fdBasisI.then poly_vectorNeg).congr (fun _ => vectorNeg_ofFn _)).both
            ((poly_fdBasisJ.then poly_vectorNeg).congr (fun _ => vectorNeg_ofFn _))).then
            poly_vectorAdd).congr (fun _ => vectorAdd_ofFn _ _)) a ha hn
    · exact runsPolyOf ((poly_constant _ _ 4).mul (((poly_fdP.then poly_fSchedule).then (poly_parameterField 5)).pow 2)) a ha
lemma runsPoly_stencilHessianRow (a : ι → FaceIndex)
    (ha : IsPoly L (fun i => (faceIndexCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).1.stencilCount)) :
    RunsPoly L stencilHessianRow a := by
  unfold stencilHessianRow
  apply runsPoly_tabulateFin_family _ _ a ha
  exact runsPoly_stencilHessianEntry (fun s : Σ i,Fin (a i).1.n => ⟨a s.1,s.2⟩)
    (isPoly_finFamily (fiP.then fN) a ha) (hn.reindex Sigma.fst)
lemma runsPoly_stencilHessian (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).stencilCount)) :
    RunsPoly L stencilHessian a := by
  unfold stencilHessian
  apply runsPoly_tabulateFin_family _ _ a ha
  exact runsPoly_stencilHessianRow (fun s : Σ i,Fin (a i).n => ⟨a s.1,s.2⟩)
    (isPoly_finFamily fN a ha) (hn.reindex Sigma.fst)
end CurrentKS.Realization

end OAI
