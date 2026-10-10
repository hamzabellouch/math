import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeMatrix
import OAI.Combinatorics.MatchingCount.Machines.TreeEnumeration
import OAI.Combinatorics.MatchingCount.Machines.TreeClosureReindex

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

lemma vertices_eq_ofFn_length (n : ℕ) (fuel : List Bool) (m : ℕ) (h : 4*fuel.length=m) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) m) i)) := by
  subst m
  exact vertices_eq_ofFn n fuel

abbrev BuildInput := (Matrix×List Bool)×List Nat

def prepare (x : BuildInput) : PathTableInput := (((x.1.1,close x.1.1),x.1.2),x.2)
def prepareRealizer : Realizer prepare := (pair (pair (pair first.fst
  (composition first.fst closeRealizer)) first.snd) second).congr (fun _=>rfl)
lemma polynomial_prepare : PolynomialTime prepareRealizer := by
  unfold prepareRealizer
  apply polynomial_congr
  have := polynomial_close
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def buildMatrix (x : BuildInput) : Matrix := materialize (prepare x)
def buildMatrixRealizer : Realizer buildMatrix := composition prepareRealizer materializeRealizer
lemma polynomial_buildMatrix : PolynomialTime buildMatrixRealizer :=
  polynomial_composition polynomial_prepare polynomial_materialize

def buildClosure (x : BuildInput) : Matrix := close (buildMatrix x)
def buildClosureRealizer : Realizer buildClosure := composition buildMatrixRealizer closeRealizer
lemma polynomial_buildClosure : PolynomialTime buildClosureRealizer :=
  polynomial_composition polynomial_buildMatrix polynomial_close

lemma source_activity_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (a b : SourceVertex (Fin n) K) :
    0≤RationalSource.activity w K a b := by
  unfold RationalSource.activity
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact pathActivity_nonneg hn w hw K q.1 q.2
  · exact le_rfl

lemma buildMatrix_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    buildMatrix ((matrixRep w,List.replicate (2*K+2) false),List.range n)=
      matrixRep (fun i j=>RationalSource.activity w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)) := by
  unfold buildMatrix prepare materialize
  rw [close_matrixRep w hw]
  rw [show BottleneckAlgorithm.close w n=RationalSource.logicalB w by simp [RationalSource.logicalB]]
  change activityMatrix (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),
    List.replicate (2*K+2) false),List.range n),
    vertices (List.range n,List.replicate (2*K+2) false))=_
  have hv : vertices (List.range n,List.replicate (2*K+2) false)=
      List.ofFn (fun i=>vertexRepr (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)) := by
    exact vertices_eq_ofFn_length n _ _ (by simp)
  rw [hv]
  exact activityMatrix_source_repr hn w hw K _ (List.length_replicate ..) _

lemma buildClosure_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    buildClosure ((matrixRep w,List.replicate (2*K+2) false),List.range n)=
      matrixRep (fun i j=>RationalSource.realB w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)) := by
  unfold buildClosure
  rw [buildMatrix_repr hn w hw K,close_matrixRep _ (fun _ _=>source_activity_nonneg hn w hw K _ _)]
  rw [BottleneckAlgorithm.close_reindex (UnitRefresh.orderedEnum (SourceVertex (Fin n) K))
    UnitRefresh.orderedEnum_lt]
  rfl
end MatchingFPRAS.ExecutableSource

end OAI
