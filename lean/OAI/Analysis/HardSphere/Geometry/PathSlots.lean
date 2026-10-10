import Mathlib
import OAI.Analysis.HardSphere.Geometry.SimplePath
import OAI.Analysis.HardSphere.Conditioning.RoutePartition

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}

def pathVertexEmbedding (p : SimplePath x y) : Fin (p.val.length+1)↪DiscreteTorus K where
  toFun i := p.val.getVert i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij
@[simp] lemma pathVertex_zero (p : SimplePath x y) : pathVertexEmbedding p 0=x := by
  exact p.val.getVert_zero
@[simp] lemma pathVertex_last (p : SimplePath x y) :
    pathVertexEmbedding p (Fin.last p.val.length)=y := p.val.getVert_length

def departureEmbedding (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) : Fin p.val.length↪J where
  toFun := pick
  inj' := by
    intro i j h
    have he := congrArg anchor h
    rw [hpick i,hpick j] at he
    have hv := (pathVertexEmbedding p).injective he
    exact Fin.ext (congrArg (fun k : Fin (p.val.length+1) ↦ k.val) hv)
def extendedAnchor (anchor : J→DiscreteTorus K) (y : DiscreteTorus K) : Option J→DiscreteTorus K :=
  fun o ↦ o.elim y anchor

lemma routeEmbedding_anchor (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc)
    (i : Fin (p.val.length+1)) :
    extendedAnchor anchor y (routeEmbedding (departureEmbedding p anchor pick hpick) i)=
      pathVertexEmbedding p i := by
  by_cases hi : i.val<p.val.length
  · have he : i=(⟨i.val,hi⟩ : Fin p.val.length).castSucc := Fin.ext rfl
    rw [he,routeEmbedding_castSucc]
    exact hpick ⟨i.val,hi⟩
  · have he : i=Fin.last p.val.length := Fin.ext (by simp only [Fin.val_last];omega)
    rw [he,routeEmbedding_last,pathVertex_last]
    rfl

lemma routeSlots_anchor_injective (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    Set.InjOn (extendedAnchor anchor y) (routeSlots (departureEmbedding p anchor pick hpick):Set (Option J)) := by
  intro a ha b hb hab
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hb
  rw [routeEmbedding_anchor,routeEmbedding_anchor] at hab
  exact congrArg _ ((pathVertexEmbedding p).injective hab)

lemma routeSlots_sites (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    (routeSlots (departureEmbedding p anchor pick hpick)).image (extendedAnchor anchor y)=p.val.support.toFinset := by
  ext v
  constructor
  · intro hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
    rw [routeEmbedding_anchor]
    exact List.mem_toFinset.mpr (p.val.getVert_mem_support i.val)
  · intro hv
    obtain ⟨n,hn,hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hv)
    refine Finset.mem_image.mpr ⟨routeEmbedding (departureEmbedding p anchor pick hpick) ⟨n,by omega⟩,
      Finset.mem_map.mpr ⟨⟨n,by omega⟩,Finset.mem_univ _,rfl⟩,?_⟩
    rw [routeEmbedding_anchor]
    exact hn

lemma simple_nearSlots_bound (R : ℕ) (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f : Fin p.val.length→J) (g : Fin q.val.length→J)
    (hf : ∀i,anchor (f i)=pathVertexEmbedding p i.castSucc)
    (hg : ∀i,anchor (g i)=pathVertexEmbedding q i.castSucc) :
    (nearSlots (torusNear K R) (extendedAnchor anchor y)
      (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))).card≤
      simpleEncounter R p q := by
  have h := nearSlots_card (torusNear K R) (extendedAnchor anchor y)
    (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))
    (routeSlots_anchor_injective p anchor f hf)
  rw [routeSlots_sites,routeSlots_sites] at h
  exact h

end HardSphere.Comparison

end
end

end

end OAI
