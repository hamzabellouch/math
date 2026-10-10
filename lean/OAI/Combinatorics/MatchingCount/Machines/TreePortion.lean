import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeColor

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def coloredRow (x : BagBuildInput×RawReal) : Key×Fraction :=
  (sourceRealKey x,path ((prepare x.1.1).1,x.2))
def coloredRowRealizer : Realizer coloredRow := (pair sourceRealKeyRealizer
  (composition (pair (composition first.fst prepareRealizer).fst second) pathRealizer)).congr (fun _=>rfl)
lemma polynomial_coloredRow : PolynomialTime coloredRowRealizer := by
  unfold coloredRowRealizer Realizer.fst
  apply polynomial_congr
  have := polynomial_sourceRealKey
  have := polynomial_prepare
  have := polynomial_path
  tree_cost

def coloredRows (x : BagBuildInput) : List (Key×Fraction) :=
  (realEdges (x.1.2,x.1.1.2)).map (fun e=>coloredRow (x,e))
def coloredRowsRealizer : Realizer coloredRows := composition (pair identity
  (composition (pair first.snd first.fst.snd) realEdgesRealizer)) (mapWith coloredRowRealizer)
lemma polynomial_coloredRows : PolynomialTime coloredRowsRealizer := by
  unfold coloredRowsRealizer
  have := polynomial_realEdges
  have := polynomial_coloredRow
  exact polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first)
      (polynomial_snd (polynomial_fst polynomial_first))) polynomial_realEdges))
    (polynomial_mapWith polynomial_coloredRow)

def colorContribution (x : Key×(Key×Fraction)) : Fraction :=
  if x.1=x.2.1 then x.2.2 else (0,1)
def colorContributionRealizer : Realizer colorContribution := (choose
  (composition (pair first second.fst) (pairEqual (pairEqual natEqual natEqual) natEqual)) second.snd
  (constant ((0,1) : Fraction))).congr (by intro x; simp only [colorContribution,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_colorContribution : PolynomialTime colorContributionRealizer := by
  unfold colorContributionRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual
  tree_cost

def realPart (x : BagBuildInput×Key) : Fraction :=
  sum ((coloredRows x.1).map (fun row=>colorContribution (x.2,row)))
def realPartRealizer : Realizer realPart := composition
  (composition (pair second (composition first coloredRowsRealizer)) (mapWith colorContributionRealizer)) sumRealizer
lemma polynomial_realPart : PolynomialTime realPartRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_coloredRows))
    (polynomial_mapWith polynomial_colorContribution)) polynomial_sum

lemma coloredRow_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (a : SourceRealEdge (Fin n) K) :
    coloredRow ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),realRepr a)=
      (sourceKey (RationalSource.coloredReal w K a),TreeFraction.repr (RationalSource.pathActivity w K a.1 a.2)) := by
  unfold coloredRow
  rw [sourceRealKey_source hn w hw K]
  unfold prepare
  dsimp only
  rw [close_matrixRep w hw,show BottleneckAlgorithm.close w n=RationalSource.logicalB w by simp [RationalSource.logicalB]]
  rw [path_source_repr hn w hw K _ (List.length_replicate ..)]

lemma realPart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    realPart ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),sourceKey e)=
      TreeFraction.repr (RationalSource.realPortion w K e) := by
  let x : BagBuildInput:=(((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)
  let es:=realEdges (List.range n,List.replicate (2*K+2) false)
  let f : RawReal→ℚ:=fun a=>if sourceRealKey (x,a)=sourceKey e then
    val (path ((prepare x.1).1,a)) else 0
  let g : SourceRealEdge (Fin n) K→ℚ:=fun a=>if RationalSource.coloredReal w K a=e then
    RationalSource.pathActivity w K a.1 a.2 else 0
  have hg (a) : 0≤g a := by
    dsimp only [g]
    split_ifs <;> first | exact pathActivity_nonneg hn w hw K _ _ | exact le_rfl
  have hrow (a : SourceRealEdge (Fin n) K) :
      colorContribution (sourceKey e,coloredRow (x,realRepr a))=TreeFraction.repr (g a) := by
    rw [coloredRow_source hn w hw K]
    simp only [colorContribution,sourceKey_injective.eq_iff]
    dsimp only [g]
    by_cases h : RationalSource.coloredReal w K a=e
    · simp only [h,ite_true]
    · simp only [h,Ne.symm h,ite_false]
      rfl
  have hf (a : SourceRealEdge (Fin n) K) : f (realRepr a)=g a := by
    have h:=coloredRow_source hn w hw K a
    have hp:=congrArg Prod.snd h
    change path ((prepare x.1).1,realRepr a)=_ at hp
    have hk:=congrArg Prod.fst h
    change sourceRealKey (x,realRepr a)=sourceKey (RationalSource.coloredReal w K a) at hk
    dsimp only [f,g]
    simp only [hk,sourceKey_injective.eq_iff,hp,val_repr (pathActivity_nonneg hn w hw K _ _)]
  have hmap : (es.map fun a=>colorContribution (sourceKey e,coloredRow (x,a)))=
      (es.map f).map TreeFraction.repr := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    have hm : a∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr ha
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hm
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hm
    simpa only [Function.comp_apply,hf] using hrow b
  unfold realPart coloredRows
  rw [List.map_map]
  change sum (es.map (fun a=>colorContribution (sourceKey e,coloredRow (x,a))))=_
  rw [hmap,sum_repr]
  · congr 1
    rw [sum_realEdges n K _ (List.length_replicate ..)]
    exact Finset.sum_congr rfl (fun a _=>hf a)
  · intro q hq
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
    have hm : a∈(realEdges (List.range n,List.replicate (2*K+2) false)).toFinset:=List.mem_toFinset.mpr ha
    rw [realEdges_finset n K _ (List.length_replicate ..)] at hm
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hf]
    exact hg b
end MatchingFPRAS.ExecutableSource

end OAI
