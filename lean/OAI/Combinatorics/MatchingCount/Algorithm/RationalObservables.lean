import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.MarkBridge

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _

def rawReweight (w w₁ : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) : ℚ :=
  if e.2.val=2*(2*K+2) then BottleneckAlgorithm.edge w₁ (source e.1) (target e.1)/
    BottleneckAlgorithm.edge w (source e.1) (target e.1) else 1

def bagReweight (w w₁ : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  1+∑ q : SourceRealEdge V K,if coloredReal w K q=e then rawReweight w w₁ K q-1 else 0
lemma bagReweight_on (w w₁ : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    bagReweight w w₁ K (coloredReal w K q)=rawReweight w w₁ K q := by
  simp only [bagReweight,(coloredReal_injective w K).eq_iff,sum_ite_eq',mem_univ,ite_true]
  ring
lemma bagReweight_off (w w₁ : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K))
    (he : ¬∃ q,coloredReal w K q=e) : bagReweight w w₁ K e=1 := by
  have hz : (∑ q : SourceRealEdge V K,if coloredReal w K q=e then rawReweight w w₁ K q-1 else 0)=0 := by
    apply sum_eq_zero
    intro q _
    exact ite_eq_right (fun h=>he ⟨q,h⟩)
  rw [bagReweight,hz,add_zero]
omit [Fintype V] [Nontrivial V] in
lemma rawReweight_cast (w w₁ : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    (rawReweight w w₁ K q:ℝ)=Enlargement.rawReweight (fun x y=>(w x y:ℝ))
      (fun x y=>(w₁ x y:ℝ)) K q := by
  simp only [rawReweight,Enlargement.rawReweight]
  split_ifs
  · simp only [Rat.cast_div,BottleneckAlgorithm.edge,logicalActivity,Switching.edgeActivity]
    split_ifs <;> rfl
  · norm_cast
lemma bagReweight_cast (w w₁ : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (bagReweight w w₁ K (sourceEdgeEquiv w K e):ℝ)=
      Enlargement.bagReweight (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K e := by
  classical
  by_cases he : ∃ q,sourceColoredReal (fun x y=>(w x y:ℝ)) K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [sourceEdgeEquiv_real,bagReweight_on]
    exact (rawReweight_cast w w₁ K q).trans (Enlargement.bagReweight_on _ _ K q).symm
  · rw [bagReweight_off w w₁ K _ ?_]
    · unfold Enlargement.bagReweight
      change ¬∃ q,sourceRealEmbedding (fun x y=>(w x y:ℝ)) K q=e at he
      rw [dite_eq_right he]
      norm_cast
    · rintro ⟨q,hq⟩
      apply he
      refine ⟨q,(sourceEdgeEquiv w K).injective ?_⟩
      rwa [sourceEdgeEquiv_real]

def observableA (w : V → V → ℚ) (K : ℕ) (a : Marked w K) : ℚ :=
  if a.2=(fun _=>0) then 1 else 0

def observableD (w w₁ : V → V → ℚ) (K : ℕ) (a : Marked w K) : ℚ :=
  if a.2=(fun _=>0) then ∏ e ∈ a.1.val,bagReweight w w₁ K e else 0

def observableProbe (w w₁ : V → V → ℚ) (K : ℕ) (e₀ : LogicalEdge V) (a : Marked w K) : ℚ :=
  if {centralEdge w K e₀}⊆a.1.val ∧
      a.2=(fun e=>if e.val∈({centralEdge w K e₀}:Finset _) then 2 else 0)
    then ∏ e ∈ a.1.val \ {centralEdge w K e₀},bagReweight w w₁ K e else 0
end MatchingFPRAS.RationalSource
namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma markedEquiv_marks_eq (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=I) inc) (r : F → I) :
    (markedEquiv e he a).2=(fun x=>r x.val) ↔ a.2=(fun x=>r (e x.val)) := by
  constructor
  · intro h
    funext x
    have hh:=congrFun h (selectedEquiv e he a.1 x)
    rw [markedEquiv_mark] at hh
    exact hh
  · intro h
    funext x
    obtain ⟨y,rfl⟩:=(selectedEquiv e he a.1).surjective x
    rw [markedEquiv_mark,congrFun h]
    rfl
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma markedEquiv_zero (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=Fin 3) inc) :
    (markedEquiv e he a).2=(fun _=>0) ↔ a.2=(fun _=>0) :=
  markedEquiv_marks_eq e he a (fun _=>0)
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma markedEquiv_probe (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=Fin 3) inc) (u : E) :
    ({e u}⊆(markedEquiv e he a).1.val ∧
      (markedEquiv e he a).2=(fun x=>if x.val∈({e u}:Finset _) then 2 else 0)) ↔
    ({u}⊆a.1.val ∧ a.2=(fun x=>if x.val∈({u}:Finset _) then 2 else 0)) := by
  rw [markedEquiv_marks_eq e he a (fun x=>if x∈({e u}:Finset F) then 2 else 0)]
  rw [singleton_subset_iff,singleton_subset_iff]
  change (e u∈a.1.val.image e ∧ _) ↔ (u∈a.1.val ∧ _)
  simp only [mem_singleton,e.injective.eq_iff,
    mem_image,exists_eq_right]
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma pmEquiv_product_erase {R : Type*} [CommMonoid R]
    (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) (M : PM inc) (u : E) (f : F → R) :
    (∏ x ∈ (pmEquiv e he M).val \ {e u},f x)=∏ x ∈ M.val \ {u},f (e x) := by
  have hh : (pmEquiv e he M).val \ {e u}=(M.val \ {u}).image e := by
    change M.val.image e \ {e u}=(M.val \ {u}).image e
    ext x
    simp only [mem_sdiff,mem_image,mem_singleton]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hu⟩
      exact ⟨y,⟨hy,fun h=>hu (congrArg e h)⟩,rfl⟩
    · rintro ⟨y,⟨hy,hu⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,fun h=>hu (e.injective h)⟩
  rw [hh]
  exact prod_image (fun _ _ _ _ h=>e.injective h)
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
lemma sourceEdgeEquiv_incidence (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) (x : SourceVertex V K) :
    (sourceEdgeEquiv w K e).Incident x ↔ e.Incident x := Iff.rfl
lemma sourceMarkedEquiv_zero (w : V → V → ℚ) (K : ℕ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (sourceMarkedEquiv w K a).2=(fun _=>0) ↔ a.2=(fun _=>0) :=
  markedEquiv_zero (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a
lemma observableA_cast (w : V → V → ℚ) (K : ℕ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableA w K (sourceMarkedEquiv w K a):ℝ)=Enlargement.observableA (fun x y=>(w x y:ℝ)) K a := by
  simp only [observableA,Enlargement.observableA,sourceMarkedEquiv_zero]
  split_ifs <;> norm_cast
lemma observableD_cast (w w₁ : V → V → ℚ) (K : ℕ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableD w w₁ K (sourceMarkedEquiv w K a):ℝ)=
      Enlargement.observableD (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K a := by
  simp only [observableD,Enlargement.observableD,sourceMarkedEquiv_zero]
  split_ifs
  · push_cast
    change matchingWeight (fun e=>(bagReweight w w₁ K e:ℝ))
      (pmEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a.1)=_
    rw [matchingWeight_pmEquiv (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K)]
    unfold matchingWeight
    apply prod_congr rfl
    intro e _
    exact bagReweight_cast w w₁ K e
  · norm_cast
lemma observableProbe_cast (w w₁ : V → V → ℚ) (K : ℕ) (u : LogicalEdge V)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableProbe w w₁ K u (sourceMarkedEquiv w K a):ℝ)=
      Enlargement.observableProbe (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K u a := by
  have hh:=markedEquiv_probe (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a
    (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)
  rw [sourceEdgeEquiv_central] at hh
  change ({centralEdge w K u}⊆(sourceMarkedEquiv w K a).1.val ∧
    (sourceMarkedEquiv w K a).2=(fun e=>if e.val∈({centralEdge w K u}:Finset _) then 2 else 0)) ↔ _ at hh
  simp only [observableProbe,Enlargement.observableProbe,hh]
  simp only [mem_singleton] at hh ⊢
  split_ifs <;> try contradiction
  · push_cast
    rw [←sourceEdgeEquiv_central w K u]
    change (∏ e ∈ (pmEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a.1).val \
      {sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)},
      (bagReweight w w₁ K e:ℝ))=_
    rw [pmEquiv_product_erase (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K)]
    refine prod_congr (by ext; simp) ?_
    intro e _
    exact bagReweight_cast w w₁ K e
  · norm_cast
end MatchingFPRAS.RationalSource

end OAI
