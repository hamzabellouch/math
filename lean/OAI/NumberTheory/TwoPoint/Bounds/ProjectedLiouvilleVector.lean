import OAI.NumberTheory.TwoPoint.Bounds.ProjectedGraphTesting
import OAI.NumberTheory.TwoPoint.Walks.RetainedLiouvilleEdges

namespace OAI

/-! The actual degree-projected Liouville test is an ambient masked scalar. -/

namespace TwoPointCorrelations

open scoped Classical

lemma projectedLiouvilleVector_eq {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (keep : ℤ → Prop) :
    coordinateProjection (fun i => keep (site i))
        (paddingTestVector Q L site integerLiouville) =
      WithLp.toLp 2 (fun i => retainedLiouvilleScalar (actualPaddingVertex Q)
        (fun n => keep n ∧ actualPaddingDegreeCut Q L n) (site i)) := by
  ext i
  by_cases hp : keep (site i) <;> by_cases hq : actualPaddingDegreeCut Q L (site i) <;>
    simp [coordinateProjection_apply, paddingTestVector, retainedLiouvilleScalar, hp, hq]

lemma projectedLiouvilleVector_star {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (keep : ℤ → Prop) (i : V) :
    star (coordinateProjection (fun i => keep (site i))
      (paddingTestVector Q L site integerLiouville) i) =
      coordinateProjection (fun i => keep (site i))
        (paddingTestVector Q L site integerLiouville) i := by
  rw [projectedLiouvilleVector_eq]
  exact retainedLiouvilleScalar_star _ _ _

end TwoPointCorrelations

end OAI
