import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeEstimator
import OAI.Combinatorics.MatchingCount.Algorithm.TreeWeights

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

lemma logicalEdges_nodup {vs : List ℕ} (hv : vs.Nodup) : (logicalEdges vs).Nodup :=
  List.Nodup.filter _ (hv.product hv)
lemma realEdges_nodup {vs : List ℕ} (hv : vs.Nodup) (fuel : List Bool) :
    (realEdges (vs,fuel)).Nodup := (logicalEdges_nodup hv).product List.nodup_range
lemma realRepr_injective {n m : ℕ} : Function.Injective (realRepr (n:=n) (m:=m)) := by
  intro a b h
  exact Prod.ext (logicalRepr_injective (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

lemma realEdges_finset (n K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2) :
    (realEdges (List.range n,fuel)).toFinset=
      Finset.univ.image (realRepr (n:=n) (m:=4*(2*K+2))) := by
  ext e
  simp only [List.mem_toFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro he
    obtain ⟨⟨a,i⟩,hi⟩:=realEdges_complete fuel e he
    exact ⟨(a,Fin.cast (by rw [hf]) i),hi⟩
  · rintro ⟨⟨a,i⟩,rfl⟩
    exact realRepr_mem fuel (a,Fin.cast (by rw [hf]) i)

lemma sum_realEdges (n K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2) (f : RawReal→ℚ) :
    ((realEdges (List.range n,fuel)).map f).sum =
      ∑ e : SourceRealEdge (Fin n) K, f (realRepr e) := by
  rw [←List.sum_toFinset f (realEdges_nodup List.nodup_range fuel),realEdges_finset n K fuel hf]
  exact Finset.sum_image (fun a _ b _ h=>realRepr_injective h)

lemma path_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),realRepr e)=
      TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2) := by
  have h:=path_repr hn w hw K fuel hf e.1 (Fin.cast (by rw [hf]) e.2)
  simpa only [Fin.cast_cast,Fin.cast_refl,Fin.val_cast,realRepr,id] using h

lemma ends_source_repr {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    (left ((List.range n,fuel),realRepr e),right ((List.range n,fuel),realRepr e))=
    (vertexRepr (atVertex source target (4*(2*K+2)) e.1 e.2.castSucc),
     vertexRepr (atVertex source target (4*(2*K+2)) e.1 e.2.succ)) := by
  apply Prod.ext
  · unfold left internalCount
    dsimp only
    rw [hf]
    exact at_repr e.1 e.2.castSucc
  · unfold right internalCount
    dsimp only
    rw [hf]
    exact at_repr e.1 e.2.succ

lemma sameEnds_source {n : ℕ} (K : ℕ) (a b x y : SourceVertex (Fin n) K) :
    sameEnds ((vertexRepr x,vertexRepr y),(vertexRepr a,vertexRepr b))=
      decide (s(a,b)=s(x,y)) := by
  simp only [sameEnds,vertexRepr_injective.eq_iff]
  congr 1
  rw [Sym2.eq_iff]
  apply propext
  constructor
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact Or.inl ⟨h₁.symm,h₂.symm⟩
    · exact Or.inr ⟨h₂.symm,h₁.symm⟩
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact Or.inl ⟨h₁.symm,h₂.symm⟩
    · exact Or.inr ⟨h₂.symm,h₁.symm⟩

lemma contribution_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (x y : SourceVertex (Fin n) K) (e : SourceRealEdge (Fin n) K) :
    contribution ((vertexRepr x,vertexRepr y),
      pathRow ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),realRepr e))=
    TreeFraction.repr (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
      then RationalSource.pathActivity w K e.1 e.2 else 0) := by
  unfold contribution pathRow
  rw [path_source_repr hn w hw K fuel hf e,ends_source_repr K fuel hf e,
    sameEnds_source K]
  simp only [decide_eq_true_eq]
  change (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
       then TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2) else TreeFraction.repr (0:ℚ))=_
  split_ifs <;> rfl

lemma pathActivity_nonneg {n : ℕ} [Nontrivial (Fin n)] (_hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (e : LogicalEdge (Fin n)) (i : Fin (4*(2*K+2)+1)) :
    0≤RationalSource.pathActivity w K e i := by
  have hB : 0≤RationalSource.logicalB w (source e) (target e) :=
    (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ _ _)
  unfold RationalSource.pathActivity RationalSource.profile
  split_ifs
  · exact hB.trans (le_max_left _ _)
  · unfold BottleneckAlgorithm.edge
    split_ifs <;> exact hw _ _
  · exact hB.trans (le_max_left _ _)

lemma activity_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (x y : SourceVertex (Fin n) K) :
    activity (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),
      (vertexRepr x,vertexRepr y))=TreeFraction.repr (RationalSource.activity w K x y) := by
  let f : RawReal→ℚ := fun e=>
    if sameEnds ((vertexRepr x,vertexRepr y),
      (left ((List.range n,fuel),e),right ((List.range n,fuel),e))) then
        (path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),e)).1 /
          ((path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),e)).2 : ℚ)
      else 0
  let es:=realEdges (List.range n,fuel)
  let g : SourceRealEdge (Fin n) K→ℚ := fun e=>
    if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
      then RationalSource.pathActivity w K e.1 e.2 else 0
  have hg (e) : 0≤g e := by
    dsimp only [g]
    split_ifs
    · exact pathActivity_nonneg hn w hw K _ _
    · exact le_rfl
  have hre (e : SourceRealEdge (Fin n) K) : f (realRepr e)=g e := by
    dsimp only [f,g]
    rw [ends_source_repr K fuel hf e,sameEnds_source K,path_source_repr hn w hw K fuel hf e]
    simp only [decide_eq_true_eq]
    change (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
       then val (TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2)) else 0)=_
    split_ifs
    · exact val_repr (pathActivity_nonneg hn w hw K _ _)
    · rfl
  have hrow (e : RawReal) (he : e∈es) :
      contribution ((vertexRepr x,vertexRepr y),pathRow
        ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e))=
        TreeFraction.repr (f e) := by
    have hm : e∈(realEdges (List.range n,fuel)).toFinset:=List.mem_toFinset.mpr he
    rw [realEdges_finset n K fuel hf] at hm
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hre]
    exact contribution_source_repr hn w hw K fuel hf x y a
  unfold activity pathTable
  rw [List.map_map]
  dsimp only [Function.comp,Prod.fst,Prod.snd]
  have hmap : (es.map fun e=>contribution ((vertexRepr x,vertexRepr y),pathRow
      ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e)))=
      (es.map f).map TreeFraction.repr := by
    rw [List.map_map]
    exact List.map_congr_left hrow
  change sum (es.map (fun e=>contribution ((vertexRepr x,vertexRepr y),pathRow
      ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e)))) = _
  rw [hmap,sum_repr]
  · congr 1
    rw [sum_realEdges n K fuel hf]
    exact Finset.sum_congr rfl (fun e _=>hre e)
  · intro q hq
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hq
    have hm : e∈(realEdges (List.range n,fuel)).toFinset:=List.mem_toFinset.mpr he
    rw [realEdges_finset n K fuel hf] at hm
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hre]
    exact hg a
end MatchingFPRAS.ExecutableSource

end OAI
