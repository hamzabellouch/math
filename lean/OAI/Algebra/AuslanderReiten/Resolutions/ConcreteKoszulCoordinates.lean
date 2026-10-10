import OAI.Algebra.AuslanderReiten.Resolutions.ConcreteKoszulCoordinateLaws

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem concreteTwoConeFiltration_row (a : ℤ) (v : twoConeMiddleHom q a) :
    (concreteTwoConeFiltration q).row a v =
      TriangleGradedSequence.connecting k (simpleSkeletonTriangle q 0)
        (evaluatedSimpleObject q) a v := rfl

theorem concreteTwoConeFiltration_column (a : ℤ) (v : twoConeTopHom q a) :
    (concreteTwoConeFiltration q).column a v =
      TriangleGradedSequence.second k (simpleSkeletonTriangle q 0) (evaluatedSimpleObject q)
        (a+1) (TriangleGradedSequence.connecting k (simpleTopTriangle q 0)
          (evaluatedSimpleObject q) a v) := rfl

def concreteKoszulCoordinates : TwoConeKoszulCoordinates (concreteTwoConeFiltration q)
    (fun a => fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (firstCoverClass q))
    (fun a => fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (secondCoverClass q)) where
  bottom := twoConeBottomCoordinate q
  middle := twoConeMiddleCoordinate q
  top := twoConeTopCoordinate q
  row_eq := concreteRowCoordinate q
  column_eq := concreteColumnCoordinate q

end ArExplicit.T

end

end OAI
