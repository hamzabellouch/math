import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeSource

namespace OAI

/-! The unordered endpoint support determines the edge permutation of a
simple graph, including the possible reversal of each edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointRelabel
open scoped Classical

variable {G H : QMARationalExchangeGraph} (vertex : Fin H.n ≃ Fin G.n)
    (hH : H.Simple) (hG : G.Simple)
    (source : ∀ e : H.Edge, ∃ f : G.Edge,
      s(vertex (H.left e),vertex (H.right e))=s(G.left f,G.right f))
    (target : ∀ f : G.Edge, ∃ e : H.Edge,
      s(vertex (H.left e),vertex (H.right e))=s(G.left f,G.right f))

def chooseEdge (e : H.Edge) : G.Edge := Classical.choose (source e)

theorem chooseEdge_spec (e : H.Edge) :
    s(vertex (H.left e),vertex (H.right e))=
      s(G.left (chooseEdge vertex source e),G.right (chooseEdge vertex source e)) :=
  Classical.choose_spec (source e)

include hH in
theorem chooseEdge_injective : Function.Injective (chooseEdge vertex source) := by
  intro e f hef
  by_contra hne
  have hp := (chooseEdge_spec vertex source e).trans
    ((congrArg (fun k => s(G.left k,G.right k)) hef).trans
      (chooseEdge_spec vertex source f).symm)
  rcases Sym2.eq_iff.mp hp with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact (hH e f hne).1 ⟨vertex.injective hl,vertex.injective hr⟩
  · exact (hH e f hne).2 ⟨vertex.injective hl,vertex.injective hr⟩

include hG in
theorem endpoint_injective : Function.Injective (fun e : G.Edge => s(G.left e,G.right e)) := by
  intro e f hef
  by_contra hne
  rcases Sym2.eq_iff.mp hef with h | h
  · exact (hG e f hne).1 h
  · exact (hG e f hne).2 h

include hG target in
theorem chooseEdge_surjective : Function.Surjective (chooseEdge vertex source) := by
  intro f
  obtain ⟨e,he⟩ := target f
  refine ⟨e,endpoint_injective hG ?_⟩
  exact (chooseEdge_spec vertex source e).symm.trans he

def edge : H.Edge ≃ G.Edge := Equiv.ofBijective (chooseEdge vertex source)
  ⟨chooseEdge_injective vertex hH source,chooseEdge_surjective vertex hG source target⟩

def flip (e : H.Edge) : Bool := decide (vertex (H.left e)≠G.left (edge vertex hH hG source target e))

theorem left (e : H.Edge) : vertex (H.left e)=
    if flip vertex hH hG source target e then G.right (edge vertex hH hG source target e)
      else G.left (edge vertex hH hG source target e) := by
  have h := chooseEdge_spec vertex source e
  change s(vertex (H.left e),vertex (H.right e))=
    s(G.left (edge vertex hH hG source target e),G.right (edge vertex hH hG source target e)) at h
  rcases Sym2.eq_iff.mp h with ⟨hl,_⟩ | ⟨hl,_⟩
  · simp only [flip,hl,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
  · have hn : vertex (H.left e)≠G.left (edge vertex hH hG source target e) := by
      rw [hl]
      exact (G.distinct _).symm
    have hf : flip vertex hH hG source target e = true := decide_eq_true hn
    simp only [hf,ite_true]
    exact hl

theorem right (e : H.Edge) : vertex (H.right e)=
    if flip vertex hH hG source target e then G.left (edge vertex hH hG source target e)
      else G.right (edge vertex hH hG source target e) := by
  have h := chooseEdge_spec vertex source e
  change s(vertex (H.left e),vertex (H.right e))=
    s(G.left (edge vertex hH hG source target e),G.right (edge vertex hH hG source target e)) at h
  rcases Sym2.eq_iff.mp h with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · simp only [flip,hl,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
    exact hr
  · have hn : vertex (H.left e)≠G.left (edge vertex hH hG source target e) := by
      rw [hl]
      exact (G.distinct _).symm
    have hf : flip vertex hH hG source target e = true := decide_eq_true hn
    simp only [hf,ite_true]
    exact hr

end ContinuumCoulomb.QuantumEndpointRelabel

end

end OAI
