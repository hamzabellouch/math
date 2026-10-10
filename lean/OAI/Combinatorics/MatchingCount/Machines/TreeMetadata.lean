import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePhantom

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
lemma arbitrary_parents_fintype (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (H : ℕ) (hH : xs.length=H) (F : Fintype (Label B H)) :
    letI := F
    parents (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent (NumberedHierarchy.parent B hsym htri (H:=H))) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_parents B hB hsym htri xs
end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceParents (x : BagBuildInput) : ExecutableDP.Parents := parents (setupHierarchy x).1
def sourceParentsRealizer : Realizer sourceParents := composition setupHierarchyRealizer.fst parentsRealizer
lemma polynomial_sourceParents : PolynomialTime sourceParentsRealizer :=
  polynomial_composition (polynomial_fst polynomial_setupHierarchy) polynomial_parents
lemma sourceParents_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceParents (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent (RationalSource.parent w K)) := by
  unfold sourceParents setupHierarchy
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  exact arbitrary_parents_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))

lemma sourceTables_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    let x : BagBuildInput:=(((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)
    sourceTables x=(sourceCatalog (RationalSource.bags w K),
      ((setupBags x,ExecutableDP.parentRep (UnitRefresh.numberedParent (RationalSource.parent w K))),
        (UnitRefresh.Materialized.plan (UnitRefresh.numberedRank
          (fun l : RationalSource.Label w K=>l.1.val))).map Fin.val)) := by
  dsimp only
  apply Prod.ext
  · exact sourceTables_catalog hn w hw K
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact sourceParents_source hn w hw K
  change rankPlan (sourceRanks _)=_
  rw [sourceRanks_source hn w hw K,rankPlan_eq]
end MatchingFPRAS.ExecutableSource

end OAI
