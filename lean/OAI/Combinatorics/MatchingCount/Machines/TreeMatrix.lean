import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeWeightsCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

abbrev MatrixInput := List WeightedEdge×List RawVertex

def activityRow (x : MatrixInput×RawVertex) : List Fraction :=
  x.1.2.map (fun y=>activity (x.1.1,(x.2,y)))
def activityRowRealizer : Realizer activityRow := (composition
  (pair (pair first.fst second) first.snd)
  (mapWith (composition (pair first.fst (pair first.snd second)) activityRealizer))).congr (fun _=>rfl)
lemma polynomial_activityRow : PolynomialTime activityRowRealizer := by
  unfold activityRowRealizer
  apply polynomial_congr
  have := polynomial_activity
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def activityMatrix (x : MatrixInput) : Matrix := x.2.map (fun v=>activityRow (x,v))
def activityMatrixRealizer : Realizer activityMatrix := composition (pair identity second) (mapWith activityRowRealizer)
lemma polynomial_activityMatrix : PolynomialTime activityMatrixRealizer := by
  exact polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_mapWith polynomial_activityRow)

def materialize (x : PathTableInput) : Matrix := activityMatrix (pathTable x,vertices (x.2,x.1.2))
def materializeRealizer : Realizer materialize := (composition (pair pathTableRealizer
  (composition (pair second first.snd) verticesRealizer)) activityMatrixRealizer).congr (fun _=>rfl)
lemma polynomial_materialize : PolynomialTime materializeRealizer := by
  unfold materializeRealizer
  apply polynomial_congr
  have := polynomial_pathTable
  have := polynomial_vertices
  have := polynomial_activityMatrix
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

lemma activityMatrix_repr {N : ℕ} (vs : Fin N→RawVertex) (tab : List WeightedEdge)
    (w : Fin N→Fin N→ℚ) (hw : ∀ i j,activity (tab,(vs i,vs j))=TreeFraction.repr (w i j)) :
    activityMatrix (tab,List.ofFn vs)=matrixRep w := by
  unfold activityMatrix activityRow matrixRep
  simp only [List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  congr 1
  funext j
  exact hw i j

lemma activityMatrix_source_repr {n N : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (v : Fin N→SourceVertex (Fin n) K) :
    activityMatrix (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),
      List.ofFn (fun i=>vertexRepr (v i)))=
    matrixRep (fun i j=>RationalSource.activity w K (v i) (v j)) := by
  apply activityMatrix_repr
  intro i j
  exact activity_source_repr hn w hw K fuel hf (v i) (v j)
end MatchingFPRAS.ExecutableSource

end OAI
