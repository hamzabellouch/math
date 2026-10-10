import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarTapeProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergedSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEndpointRelabel

namespace OAI

/-! The actual merged planar tape and the canonical crossing graph have
the same unordered edges, with an explicit finite edge equivalence. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram
open scoped Classical

def rawGraph (x : Input) (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds x.1.1.1 x.1.1.2.1 x.1.1.2.2 hb hn

def graph (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds x.1.1.1 (merged x) x.1.1.2.2
    (QuantumListMerge.bounded _ _) (QuantumListMerge.noLoops hn)

private theorem fin_pair_eq {n : ℕ} {a b c d : Fin n}
    (h : s(a.val,b.val) = s(c.val,d.val)) : s(a,b) = s(c,d) := by
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext ha,Fin.ext hb⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext ha,Fin.ext hb⟩)

theorem graph_source (x : Input) (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) (e : (graph x hn).Edge) :
    ∃ f : (rawGraph x hb hn).Edge,
      s((graph x hn).left e,(graph x hn).right e) =
        s((rawGraph x hb hn).left f,(rawGraph x hb hn).right f) := by
  obtain ⟨b,hb',hpair⟩ := QuantumListMerge.value_edge_source x.1.1.1 x.1.1.2.1
    (List.get_mem (merged x) e)
  obtain ⟨f,hf⟩ := List.mem_iff_get.mp hb'
  refine ⟨f,fin_pair_eq ?_⟩
  change s(((merged x).get e).1,((merged x).get e).2.1) =
    s((x.1.1.2.1.get f).1,(x.1.1.2.1.get f).2.1)
  rwa [hf]

theorem graph_target (x : Input) (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) (f : (rawGraph x hb hn).Edge) :
    ∃ e : (graph x hn).Edge,
      s((graph x hn).left e,(graph x hn).right e) =
        s((rawGraph x hb hn).left f,(rawGraph x hb hn).right f) := by
  obtain ⟨b,hb',hpair⟩ := QuantumListMerge.value_edge_target hb (List.get_mem x.1.1.2.1 f)
  obtain ⟨e,he⟩ := List.mem_iff_get.mp hb'
  refine ⟨e,fin_pair_eq ?_⟩
  change s(((QuantumListMerge.value x.1.1.1 x.1.1.2.1).get e).1,
    ((QuantumListMerge.value x.1.1.1 x.1.1.2.1).get e).2.1) =
    s((x.1.1.2.1.get f).1,(x.1.1.2.1.get f).2.1)
  rwa [he]

theorem graph_simple (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    (graph x hn).Simple := by
  intro e f hef
  have h := QuantumListMerge.value_simple hn e f hef
  constructor
  · rintro ⟨hl,hr⟩
    exact h.1 ⟨congrArg Fin.val hl,congrArg Fin.val hr⟩
  · rintro ⟨hl,hr⟩
    exact h.2 ⟨congrArg Fin.val hl,congrArg Fin.val hr⟩

section Canonical
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1)
    (vertex : Fin x.1.1.1 ≃ Fin (P.crossingOutput N hD).n)
    (forward : ∀ e : (rawGraph x hb hn).Edge, ∃ f : (P.crossingOutput N hD).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))
    (backward : ∀ f : (P.crossingOutput N hD).Edge, ∃ e : (rawGraph x hb hn).Edge,
      s(vertex ((rawGraph x hb hn).left e),vertex ((rawGraph x hb hn).right e)) =
        s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f))

include forward in
theorem canonical_source (e : (graph x hn).Edge) :
    ∃ f : (P.crossingOutput N hD).merge.Edge,
      s(vertex ((graph x hn).left e),vertex ((graph x hn).right e)) =
        s((P.crossingOutput N hD).merge.left f,(P.crossingOutput N hD).merge.right f) := by
  obtain ⟨a,ha⟩ := graph_source x hb hn e
  obtain ⟨b,hb'⟩ := forward a
  obtain ⟨f,hf⟩ := (P.crossingOutput N hD).merge_unordered_target b
  exact ⟨f,(qmaUnorderedPair_map vertex ha).trans (hb'.trans hf.symm)⟩

include backward in
theorem canonical_target (f : (P.crossingOutput N hD).merge.Edge) :
    ∃ e : (graph x hn).Edge,
      s(vertex ((graph x hn).left e),vertex ((graph x hn).right e)) =
        s((P.crossingOutput N hD).merge.left f,(P.crossingOutput N hD).merge.right f) := by
  obtain ⟨b,hb'⟩ := (P.crossingOutput N hD).merge_unordered_source f
  obtain ⟨a,ha⟩ := backward b
  obtain ⟨e,he⟩ := graph_target x hb hn a
  exact ⟨e,(qmaUnorderedPair_map vertex he).trans (ha.trans hb'.symm)⟩

def edge : (graph x hn).Edge ≃ (P.crossingOutput N hD).merge.Edge :=
  QuantumEndpointRelabel.edge vertex (graph_simple x hn) (P.crossingOutput N hD).merge_simple
    (canonical_source P N hD x hb hn vertex forward)
    (canonical_target P N hD x hb hn vertex backward)

theorem edge_endpoints (e : (graph x hn).Edge) :
    s(vertex ((graph x hn).left e),vertex ((graph x hn).right e)) =
      s((P.crossingOutput N hD).merge.left (edge P N hD x hb hn vertex forward backward e),
        (P.crossingOutput N hD).merge.right (edge P N hD x hb hn vertex forward backward e)) :=
  QuantumEndpointRelabel.chooseEdge_spec
    (G := (P.crossingOutput N hD).merge) (H := graph x hn) vertex
    (canonical_source P N hD x hb hn vertex forward) e

end Canonical
end ContinuumCoulomb.QuantumPlanarTapeGeometry

end

end OAI
