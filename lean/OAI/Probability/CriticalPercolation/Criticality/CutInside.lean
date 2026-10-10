import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf
import OAI.Probability.CriticalPercolation.GraphGeometry.Link2

namespace OAI

section
section CurrentModule3
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def cutInside (S : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ S then (G.ends e).out.1 else (G.ends e).out.2

def cutOutside (S : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ S then (G.ends e).out.2 else (G.ends e).out.1

def IsCut (S : Set V) (e : E) : Prop := cutInside G S e ∈ S ∧ cutOutside G S e ∉ S

lemma cut_ends (S : Set V) (e : E) :
    G.ends e = s(cutInside G S e, cutOutside G S e) := by
  unfold cutInside cutOutside
  split_ifs
  · exact (G.ends e).out_eq.symm
  · exact (G.ends e).out_eq.symm.trans (Sym2.eq_swap)

lemma cut_orientation {S : Set V} {e : E} {x y : V}
    (he : G.ends e = s(x,y)) (hx : x ∈ S) (hy : y ∉ S) :
    cutInside G S e = x ∧ cutOutside G S e = y := by
  have h : s((G.ends e).out.1,(G.ends e).out.2) = s(x,y) := (G.ends e).out_eq.trans he
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · change (G.ends e).out.1 = x at h1
    change (G.ends e).out.2 = y at h2
    simp only [cutInside,cutOutside,h1,h2,ite_eq_left hx,and_self]
  · change (G.ends e).out.1 = y at h1
    change (G.ends e).out.2 = x at h2
    simp only [cutInside,cutOutside,h1,h2,ite_eq_right hy,and_self]

lemma boundaryReach_iff_cut (S : Set V) (H : SimpleGraph V) (o : V) (e : E) :
    boundaryReach G Sᶜ H o e ↔ IsCut G S e ∧ H.Reachable o (cutInside G S e) := by
  constructor
  · rintro ⟨x,y,he,hx,hy,hr⟩
    change y ∉ S at hy
    have hh := cut_orientation G he (not_not.mp hx) hy
    exact ⟨by simpa only [IsCut,hh.1,hh.2] using And.intro (not_not.mp hx) hy,
      by simpa only [hh.1] using hr⟩
  · rintro ⟨hc,hr⟩
    exact ⟨_,_,cut_ends G S e,not_not.mpr hc.1,hc.2,hr⟩

def internalIncident (S C : Set V) : Set E :=
  {e | e ∈ G.incidentEdges C ∧ ∀ v ∈ G.ends e, v ∈ S}

def internalCluster (S : Set V) (o : V) (ω : Set E) : Set V :=
  component (delete (G.openGraph ω) Sᶜ) o

lemma internalCluster_self (S : Set V) (o : V) (ω : Set E) :
    o ∈ internalCluster G S o ω := .refl _

lemma internalCluster_subset (S : Set V) {o : V} (ho : o ∈ S) (ω : Set E) :
    internalCluster G S o ω ⊆ S := by
  intro v hv
  exact reachable_mem_of_closed (H := delete (G.openGraph ω) Sᶜ)
    (U := S) (fun {_ _} _ h => not_not.mp h.2.2) ho hv

lemma internal_adj_eq {S C : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ internalIncident G S C, e ∈ ω ↔ e ∈ ω') {x y : V} (hx : x ∈ C) :
    (delete (G.openGraph ω) Sᶜ).Adj x y ↔ (delete (G.openGraph ω') Sᶜ).Adj x y := by
  have hh (e) (he : G.ends e = s(x,y)) (hxS : x ∈ S) (hyS : y ∈ S) :
      e ∈ internalIncident G S C := by
    refine ⟨⟨x,hx,by rw [he]; simp⟩,?_⟩
    intro v hv
    rw [he,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl <;> assumption
  constructor
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hxs,hys⟩
    exact ⟨⟨⟨e,(hω e (hh e hend (not_not.mp hxs) (not_not.mp hys))).mp he,hend⟩,hne⟩,hxs,hys⟩
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hxs,hys⟩
    exact ⟨⟨⟨e,(hω e (hh e hend (not_not.mp hxs) (not_not.mp hys))).mpr he,hend⟩,hne⟩,hxs,hys⟩

lemma internalCluster_eq_of_incident {S C : Set V} {o : V} {ω ω' : Set E}
    (hC : internalCluster G S o ω = C)
    (hω : ∀ e ∈ internalIncident G S C, e ∈ ω ↔ e ∈ ω') :
    internalCluster G S o ω' = C := by
  change component (delete (G.openGraph ω') Sᶜ) o = C
  rw [← roots_singleton]
  exact roots_eq_of_adj_eq_incident
    (by simpa only [roots_singleton, internalCluster] using hC)
    (fun {_ _} hx => internal_adj_eq G hω hx)

lemma dependsOn_internalCluster (S C : Set V) (o : V) :
    DependsOn (fun ω : Set E => internalCluster G S o ω = C) (internalIncident G S C) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => internalCluster_eq_of_incident G h (fun e he => (hω e he).to_iff),
    fun h => internalCluster_eq_of_incident G h (fun e he => (hω e he).symm.to_iff)⟩

lemma last_exit {H : SimpleGraph V} {C : Set V} {o v : V}
    (ho : o ∈ C) (hv : v ∉ C) (hr : H.Reachable o v) :
    ∃ x ∈ C, ∃ y ∉ C, H.Adj x y ∧ (delete H C).Reachable y v := by
  have hh : ∀ z, H.Reachable v z →
      (z ∉ C ∧ (delete H C).Reachable v z) ∨
        ∃ x ∈ C, ∃ y ∉ C, H.Adj x y ∧ (delete H C).Reachable y v := by
    intro z hz
    rw [SimpleGraph.reachable_iff_reflTransGen] at hz
    induction hz with
    | refl => exact Or.inl ⟨hv,.refl _⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hva⟩ | ih
      · by_cases hb : b ∈ C
        · exact Or.inr ⟨b,hb,a,ha,hab.symm,hva.symm⟩
        · exact Or.inl ⟨hb,hva.trans (SimpleGraph.Adj.reachable ⟨hab,ha,hb⟩)⟩
      · exact Or.inr ih
  exact (hh o hr.symm).resolve_left (fun h => h.1 ho)

lemma internalCluster_exit (S : Set V) (o : V) (ho : o ∈ S) (ω : Set E) {v : V}
    (hv : v ∉ S) (hr : (G.openGraph ω).Reachable o v) :
    ∃ e : E, IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω ∧ e ∈ ω ∧
      (delete (G.openGraph ω) (internalCluster G S o ω)).Reachable (cutOutside G S e) v := by
  obtain ⟨x,hx,y,hy,hxy,hyv⟩ := last_exit (internalCluster_self G S o ω)
    (fun hc => hv (internalCluster_subset G S ho ω hc)) hr
  have hxS : x ∈ S := internalCluster_subset G S ho ω hx
  have hyS : y ∉ S := by
    intro hyS
    exact hy (hx.trans (SimpleGraph.Adj.reachable ⟨hxy,not_not.mpr hxS,not_not.mpr hyS⟩))
  obtain ⟨⟨e,he,hend⟩,_hne⟩ := hxy
  obtain ⟨hi,ho'⟩ := cut_orientation G hend hxS hyS
  exact ⟨e,by simpa only [IsCut,hi,ho'] using And.intro hxS hyS,
    by rwa [hi],he,by rwa [ho']⟩

lemma cut_not_internalIncident {S C : Set V} {e : E} (hc : IsCut G S e) :
    e ∉ internalIncident G S C := by
  intro h
  apply hc.2
  apply h.2
  rw [cut_ends G S e]
  simp

lemma delete_update_incident {C : Set V} {e : E} (he : e ∈ G.incidentEdges C)
    (ω : Set E) (b : Prop) :
    delete (G.openGraph (Function.update ω e b)) C = delete (G.openGraph ω) C := by
  apply G.delete_openGraph_dependsOn C
  intro j hj
  have hje : j ≠ e := by rintro rfl; exact hj he
  exact Function.update_of_ne hje _ _

end CriticalPercolation.Sharpness
end
end CurrentModule3

end

end OAI
