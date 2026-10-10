import OAI.Algebra.AuslanderReiten.Resolutions.ConcreteKoszulRow
import OAI.Algebra.AuslanderReiten.Resolutions.ConcreteKoszulColumn
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

abbrev firstCoverOperator (a : ℤ) :=
  fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (firstCoverClass q)
abbrev secondCoverOperator (a : ℤ) :=
  fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (secondCoverClass q)

theorem concreteRowCoordinate (a : ℤ) (v : twoConeMiddleHom q a) :
    twoConeBottomCoordinate q (a+1) ((concreteTwoConeFiltration q).row a v) =
      TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-2+3=a+1)
        (TateKoszul.row (x := firstCoverOperator q) (y := secondCoverOperator q)
          (a-2) (twoConeMiddleCoordinate q a v)) := by
  have h := congrArg (TateKoszul.degreeEquiv (k := k) H₀
    (by omega : (a+1)-((0:ℕ):ℤ)=a+1)) (simpleSkeletonRow_fullHom q a v)
  exact h.trans (degreeEquiv_trans_apply _ _ _)

theorem concreteColumnCoordinate (a : ℤ) (v : twoConeTopHom q a) :
    twoConeMiddleCoordinate q (a+1) ((concreteTwoConeFiltration q).column a v) =
      ((TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=a+1-2)).prodCongr
        (TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=a+1-2)))
        (TateKoszul.column (x := firstCoverOperator q) (y := secondCoverOperator q)
          (a-4) (twoConeTopCoordinate q a v)) := by
  apply Prod.ext
  · exact simpleTopColumn_fst q a v
  · exact simpleTopColumn_snd q a v

end ArExplicit.T

end

end OAI
