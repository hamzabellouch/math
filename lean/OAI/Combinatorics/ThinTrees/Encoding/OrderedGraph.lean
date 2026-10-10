import Mathlib
import OAI.Combinatorics.ThinTrees.Signing.Realization

namespace OAI

/-! Ordered graph. -/

section

namespace AlgorithmicThinTrees.OrderedGraph
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def edgeEmbedding (F : Finset (Fin m)) : Fin F.card ↪ Fin m :=
  (F.orderEmbOfFin rfl).toEmbedding
def restrict (F : Finset (Fin m)) : MultiGraph n F.card where
  left e := G.left (edgeEmbedding F e)
  right e := G.right (edgeEmbedding F e)
  loopless e := G.loopless (edgeEmbedding F e)
def liftEdges (F : Finset (Fin m)) (T : Finset (Fin F.card)) : Finset (Fin m) :=
  T.map (edgeEmbedding F)
noncomputable def lowerEdges (F T : Finset (Fin m)) : Finset (Fin F.card) :=
  T.preimage (edgeEmbedding F) (edgeEmbedding F).injective.injOn

lemma embedding_mem (F : Finset (Fin m)) (e : Fin F.card) : edgeEmbedding F e ∈ F :=
  F.orderEmbOfFin_mem rfl e
lemma embedding_surj (F : Finset (Fin m)) {e : Fin m} (he : e ∈ F) :
    ∃i : Fin F.card, edgeEmbedding F i=e := by
  refine ⟨(F.orderIsoOfFin rfl).symm ⟨e,he⟩,?_⟩
  change ((F.orderIsoOfFin rfl) ((F.orderIsoOfFin rfl).symm ⟨e,he⟩)).val=e
  simp
lemma lift_univ (F : Finset (Fin m)) : liftEdges F univ=F := by
  ext e
  simp only [liftEdges,mem_map,mem_univ,true_and]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ embedding_mem F i, embedding_surj F⟩
lemma lift_lower (F T : Finset (Fin m)) (hT : T ⊆ F) : liftEdges F (lowerEdges F T)=T := by
  ext e
  simp only [liftEdges,lowerEdges,mem_map,mem_preimage]
  refine ⟨fun ⟨i,hi,hie⟩ => hie ▸ hi,fun he => ?_⟩
  obtain ⟨i,rfl⟩ := embedding_surj F (hT he)
  exact ⟨i,he,rfl⟩
lemma restrict_cut (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    liftEdges F ((restrict G F).cut T S)=G.cut (liftEdges F T) S := by
  ext e
  simp only [liftEdges,cut,mem_map,mem_filter]
  constructor
  · rintro ⟨i,⟨hi,hc⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hc⟩
  · rintro ⟨⟨i,hi,rfl⟩,hc⟩
    exact ⟨i,⟨hi,hc⟩,rfl⟩
lemma restrict_cut_card (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    ((restrict G F).cut T S).card=(G.cut (liftEdges F T) S).card := by
  rw [←restrict_cut G]
  exact (card_map _).symm
lemma restrict_connected (F : Finset (Fin m)) (T : Finset (Fin F.card)) :
    (restrict G F).Connected T ↔ G.Connected (liftEdges F T) := by
  unfold Connected
  constructor <;> intro h S hS hS'
  · rw [←restrict_cut G]
    exact map_nonempty.mpr (h S hS hS')
  · apply (map_nonempty (f := edgeEmbedding F)).mp
    change (liftEdges F ((restrict G F).cut T S)).Nonempty
    rw [restrict_cut G]
    exact h S hS hS'
lemma restrict_spanningTree (F : Finset (Fin m)) (T : Finset (Fin F.card)) :
    (restrict G F).SpanningTree T ↔ G.SpanningTree (liftEdges F T) := by
  constructor
  · rintro ⟨hc,hmin⟩
    refine ⟨(restrict_connected G F T).mp hc,?_⟩
    intro e he hh
    obtain ⟨i,hi,rfl⟩ := mem_map.mp he
    apply hmin i hi
    apply (restrict_connected G F (T.erase i)).mpr
    simpa only [liftEdges,map_erase] using hh
  · rintro ⟨hc,hmin⟩
    refine ⟨(restrict_connected G F T).mpr hc,?_⟩
    intro e he hh
    apply hmin (edgeEmbedding F e) (mem_map.mpr ⟨e,he,rfl⟩)
    have hh' := (restrict_connected G F (T.erase e)).mp hh
    simpa only [liftEdges,map_erase] using hh'
lemma restrict_packable (F : Finset (Fin m)) {r : ℕ} (h : G.TreePackable F r) :
    (restrict G F).TreePackable univ r := by
  obtain ⟨T,hT,hd⟩ := h
  refine ⟨fun i => lowerEdges F (T i),fun i => ⟨subset_univ _,?_⟩,?_⟩
  · apply (restrict_spanningTree G F _).mpr
    rw [lift_lower F (T i) (hT i).1]
    exact (hT i).2
  · intro i j hij
    exact disjoint_preimage (hd hij)
end AlgorithmicThinTrees.OrderedGraph
end

end OAI
