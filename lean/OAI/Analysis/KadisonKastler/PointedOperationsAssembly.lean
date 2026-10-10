import OAI.Analysis.KadisonKastler.PublishedPointedOperations
import OAI.Analysis.KadisonKastler.PointedCyclicEquivalence
import OAI.Analysis.KadisonKastler.PointedMatrixSum

namespace OAI

/-! # Assembling the pointed-product operations

The sum and reindexing clauses are proved from the finite-site identities.
Only the concrete lambda product construction remains as an argument here.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

theorem publishedPointedMatrixOperations_of_powers
    (hp : Nonempty (PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda))) :
    PublishedPointedMatrixOperations.{u} where
  powers := hp
  sum := by
    intro I J _ _ H K _ _ _ _ _ _ M N Ω ξ ν η S T
    exact pointedMatrixSites_sum S T
  reindex := by
    intro I J _ _ H K _ _ _ _ _ _ M N Ω ξ ν η S T e h
    exact S.exists_reindex_unitary T e h

end

end KadisonKastler

end OAI
