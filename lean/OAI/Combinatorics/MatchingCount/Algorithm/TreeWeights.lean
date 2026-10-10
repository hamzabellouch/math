import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeProfile
import OAI.Combinatorics.MatchingCount.Graphs.TreeGeometry

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Polynomial Enlargement RealGeometry

abbrev PathData := (Matrix×Matrix)×List Bool

def path (x : PathData×RawReal) : Fraction :=
  profile ((x.1.2,(cell (x.1.1.2,x.2.1),
    (height (x.1.1.2,x.2.1.1),(height (x.1.1.2,x.2.1.2),cell (x.1.1.1,x.2.1))))),x.2.2)
def pathRealizer : Realizer path :=
  (composition (pair (pair first.snd (pair
    (composition (pair first.fst.snd second.fst) cellRealizer)
    (pair (composition (pair first.fst.snd second.fst.fst) heightRealizer)
      (pair (composition (pair first.fst.snd second.fst.snd) heightRealizer)
        (composition (pair first.fst.fst second.fst) cellRealizer))))) second.snd) profileRealizer).congr (fun _=>rfl)
lemma polynomial_path : PolynomialTime pathRealizer := by
  unfold pathRealizer
  apply polynomial_congr
  have := polynomial_cell
  have := polynomial_height
  have := polynomial_profile
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

lemma path_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : LogicalEdge (Fin n)) (i : Fin (4*fuel.length+1)) :
    path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),(logicalRepr e,i.val))=
      TreeFraction.repr (RationalSource.pathActivity w K e (Fin.cast (by rw [hf]) i)) := by
  have hB : ∀ a b,0≤RationalSource.logicalB w a b := by
    intro a b
    exact (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ a b)
  have hHt : ∀ a,0≤RationalSource.height w a := by
    intro a
    obtain ⟨b,hb⟩:=Counting.others_nonempty hn a
    exact (hB a b).trans (Finset.le_sup' _ hb)
  have hheight (a : Fin n) : height (matrixRep (RationalSource.logicalB w),a.val)=
      TreeFraction.repr (RationalSource.height w a) := by
    exact height_rep hn _ hB a
  rw [path,logicalRepr,cell_matrixRep,cell_matrixRep,hheight,hheight]
  rw [profile_repr fuel _ _ _ _ (hB _ _) (hHt _) (hHt _) (hw _ _) i]
  congr 1
  have he : BottleneckAlgorithm.edge w (source e) (target e)=w (source e) (target e) := by
    have hp : source e<target e := e.property
    simp only [BottleneckAlgorithm.edge,ite_eq_left hp]
  rw [RationalSource.pathActivity,he]
  simp only [RationalSource.profile,Fin.val_cast,hf,source,target]

def vertexEqual : Realizer (fun x : RawVertex×RawVertex=>decide (x.1=x.2)) :=
  sumEqual natEqual (pairEqual (pairEqual natEqual natEqual) natEqual)
lemma polynomial_vertexEqual : PolynomialTime vertexEqual :=
  polynomial_sumEqual polynomial_natEqual (polynomial_pairEqual
    (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual)

def sameEnds (x : (RawVertex×RawVertex)×(RawVertex×RawVertex)) : Bool :=
  decide ((x.1.1=x.2.1 ∧ x.1.2=x.2.2) ∨ (x.1.1=x.2.2 ∧ x.1.2=x.2.1))
def sameEndsRealizer : Realizer sameEnds :=
  (composition (pair
    (composition (pair (composition (pair first.fst second.fst) vertexEqual)
      (composition (pair first.snd second.snd) vertexEqual)) boolAnd)
    (composition (pair (composition (pair first.fst second.snd) vertexEqual)
      (composition (pair first.snd second.fst) vertexEqual)) boolAnd)) boolOr).congr (by
        intro x; simp [sameEnds])
lemma polynomial_sameEnds : PolynomialTime sameEndsRealizer := by
  unfold sameEndsRealizer
  apply polynomial_congr
  have := polynomial_vertexEqual
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
lemma sameEnds_sym2 (a b c d : RawVertex) : sameEnds ((a,b),(c,d))=decide (s(a,b)=s(c,d)) := by
  simp only [sameEnds,Sym2.eq_iff]

abbrev WeightedEdge := (RawVertex×RawVertex)×Fraction
abbrev PathTableInput := PathData×List ℕ

def pathRow (x : PathTableInput×RawReal) : WeightedEdge :=
  ((left ((x.1.2,x.1.1.2),x.2),right ((x.1.2,x.1.1.2),x.2)),path (x.1.1,x.2))
def pathRowRealizer : Realizer pathRow :=
  (pair (pair (composition (pair (pair first.snd first.fst.snd) second) leftRealizer)
    (composition (pair (pair first.snd first.fst.snd) second) rightRealizer))
      (composition (pair first.fst second) pathRealizer)).congr (fun _=>rfl)
lemma polynomial_pathRow : PolynomialTime pathRowRealizer := by
  unfold pathRowRealizer
  apply polynomial_congr
  have := polynomial_left
  have := polynomial_right
  have := polynomial_path
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def pathTable (x : PathTableInput) : List WeightedEdge :=
  (realEdges (x.2,x.1.2)).map (fun e=>pathRow (x,e))
def pathTableRealizer : Realizer pathTable :=
  (composition (pair identity (composition (pair second first.snd) realEdgesRealizer)) (mapWith pathRowRealizer)).congr (fun _=>rfl)
lemma polynomial_pathTable : PolynomialTime pathTableRealizer := by
  unfold pathTableRealizer
  apply polynomial_congr
  have := polynomial_realEdges
  have := polynomial_mapWith polynomial_pathRow
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def contribution (x : (RawVertex×RawVertex)×WeightedEdge) : Fraction :=
  if sameEnds (x.1,x.2.1) then x.2.2 else (0,1)
def contributionRealizer : Realizer contribution :=
  (choose (composition (pair first second.fst) sameEndsRealizer) second.snd (constant (0,1))).congr (fun _=>rfl)
lemma polynomial_contribution : PolynomialTime contributionRealizer := by
  unfold contributionRealizer
  apply polynomial_congr
  have := polynomial_sameEnds
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def activity (x : List WeightedEdge×(RawVertex×RawVertex)) : Fraction :=
  sum (x.1.map (fun e=>contribution (x.2,e)))
def activityRealizer : Realizer activity :=
  (composition (composition (pair second first) (mapWith contributionRealizer)) sumRealizer).congr (fun _=>rfl)
lemma polynomial_activity : PolynomialTime activityRealizer := by
  unfold activityRealizer
  apply polynomial_congr
  have := polynomial_mapWith polynomial_contribution
  have := polynomial_sum
  tree_cost
end MatchingFPRAS.ExecutableSource

end OAI
