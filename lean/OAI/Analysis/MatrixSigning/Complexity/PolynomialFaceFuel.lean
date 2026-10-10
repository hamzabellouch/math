import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOptimize
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFind
import OAI.Analysis.MatrixSigning.Realization.FaceRunRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceBasics
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCurvature

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance size_minDatum : FoldSize ((first ratCode ratCode).min (second ratCode ratCode)) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  let L := (prodCode ratCode vectorCode (s,xs)).length
  have hs : (ratCode s).length≤L := le_prodCode_left (s,xs)
  have hy : (vectorCode ys).length≤L := (prefix_code_length ratCode xs ys zs he).trans (le_prodCode_right (s,xs))
  exact foldl_property (fun a : ℚ => (ratCode a).length≤L) ys s hs (by
    intro x hx a ha
    change (ratCode (min a x)).length≤L
    rw [min_def]
    split
    · exact ha
    · exact (mem_length_le_code ys hx).trans hy)
instance poly_minList : PolyTime minList := by unfold minList;apply poly_congr
instance poly_fUniformDrop : PolyTime fUniformDrop := by unfold fUniformDrop;apply poly_congr
instance poly_packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    [PolyTime p] [PolyTime y] : PolyTime (packFace p y) := by
  unfold packFace;apply poly_changeOutput
instance poly_faceStart : PolyTime faceStart := by
  unfold faceStart
  refine @poly_packFace _ _ _ _ _ _ ?_ ?_
  · exact poly_identity _
  · apply poly_congr
variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_fFuel (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length))
    (hn : IsPoly L (fun i => Descent.fuel (RationalFace.uniformDrop (a i).d (a i).N (a i).nu (a i).lam))) :
    RunsPoly L fFuel a := by
  unfold fFuel
  apply RunsPoly.then_poly
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_ratCeil _ hw
  exact hn.mono (fun i => Nat.le_succ _)
end CurrentKS.Realization

end

end OAI
