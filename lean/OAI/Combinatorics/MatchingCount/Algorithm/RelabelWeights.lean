import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.RelabelMore

namespace OAI

namespace MatchingFPRAS.Enlargement
open Transport

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
noncomputable local instance relabelWeightsSourceLabelDecidableEq (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance relabelWeightsSourceBagEdgeFintype (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _
lemma realPortion_on (w : V → V → ℝ) (K : ℕ) (q : SourceRealEdge V K) :
    sourceRealPortion w K (sourceColoredReal w K q)=sourceRealActivity w K q := by
  classical
  exact edgeExtension_on (sourceRealEmbedding w K) (sourceRealActivity w K) q
lemma realPortion_off (w : V → V → ℝ) (K : ℕ) (e : BagEdge (sourceBags w K))
    (he : ¬∃ q,sourceColoredReal w K q=e) : sourceRealPortion w K e=0 := by
  classical
  exact edgeExtension_off (sourceRealEmbedding w K) (sourceRealActivity w K) e he
end MatchingFPRAS.Enlargement
namespace MatchingFPRAS.RationalSource
open MatchingFPRAS Transport Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable def sourceEdgeEquiv (w : V → V → ℚ) (K : ℕ) :
    BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K) ≃ BagEdge (bags w K) :=
  relabelEdgeEquiv (labelsEquiv w K) (source_bags_equiv w K)
lemma sourceEdgeEquiv_real (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    sourceEdgeEquiv w K (sourceColoredReal (fun x y=>(w x y:ℝ)) K q)=coloredReal w K q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact labelsEquiv_edgeLabel w K q
lemma sourceEdgeEquiv_color (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (sourceEdgeEquiv w K e).color=labelsEquiv w K e.color := rfl
lemma bagHeight_cast (w : V → V → ℚ) (K : ℕ) (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (bagHeight w K (labelsEquiv w K l):ℝ)=Enlargement.bagHeight (fun x y=>(w x y:ℝ)) K l := by
  simp only [bagHeight,Enlargement.bagHeight,labelsEquiv_level]
  norm_cast
lemma realPortion_cast (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (realPortion w K (sourceEdgeEquiv w K e):ℝ)=sourceRealPortion (fun x y=>(w x y:ℝ)) K e := by
  classical
  by_cases he : ∃ q,sourceColoredReal (fun x y=>(w x y:ℝ)) K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [sourceEdgeEquiv_real,realPortion_on,Enlargement.realPortion_on]
    exact pathActivity_cast w K q.1 q.2
  · rw [realPortion_off w K _ ?_,Enlargement.realPortion_off _ _ _ he]
    norm_num
    rintro ⟨q,hq⟩
    apply he
    refine ⟨q,(sourceEdgeEquiv w K).injective ?_⟩
    rwa [sourceEdgeEquiv_real]
lemma bagWeight_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (bagWeight w K D (sourceEdgeEquiv w K e):ℝ)=sourceBagWeight (fun x y=>(w x y:ℝ)) K D e := by
  simp only [bagWeight,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,realPortion_cast,
    sourceEdgeEquiv_color,bagHeight_cast,sourceBagWeight]
  rfl
end MatchingFPRAS.RationalSource

end OAI
