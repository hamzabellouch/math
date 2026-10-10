import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceRunRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceChoice
import OAI.Analysis.MatrixSigning.Complexity.PolynomialBranchFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
lemma runsPoly_packFace {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    (a : ι → α) (hp : RunsPoly L p a) (hy : RunsPoly L y a) :
    RunsPoly L (packFace p y) a := by
  unfold packFace
  apply RunsPoly.changeOutput
  exact (hp.then_poly _).both ((hp.then_poly _).both (hy.both (hp.then_poly _)))
lemma runsPoly_faNextBase (a : ι → FaceActive)
    (ha : IsPoly L (fun i => (activeFaceCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).val.stencilCount))
    (hs : IsPoly L (fun i => (a i).val.scoreCount)) : RunsPoly L faNextBase a := by
  unfold faNextBase
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both (RunsPoly.of_poly _ a ha)
  apply RunsPoly.then_poly
  apply RunsPoly.changeOutput
  exact (RunsPoly.of_poly _ a ha).both (runsPoly_faChoice a ha hn hs)
lemma runsPoly_faceNext (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly (fun i : {i // (a i).n≠0} => L i.val) (fun i => (a i.val).stencilCount))
    (hs : IsPoly (fun i : {i // (a i).n≠0} => L i.val) (fun i => (a i.val).scoreCount)) :
    RunsPoly L faceNext a := by
  unfold faceNext
  apply RunsPoly.congr
  apply RunsPoly.dite_families (RunsPoly.of_poly _ a ha)
  · apply RunsPoly.reindex
    exact RunsPoly.of_poly (identity faceCode) _ (ha.reindex Subtype.val)
  · apply runsPoly_packFace
    · exact RunsPoly.of_poly faP _ (ha.reindex Subtype.val)
    · exact runsPoly_faNextBase _ (ha.reindex Subtype.val) hn hs
end CurrentKS.Realization

end

end OAI
