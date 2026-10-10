import OAI.Combinatorics.ThinTrees.HierarchyResponse

namespace OAI

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Classical
namespace StrongThinTree.MultiGraph

theorem simultaneous_response_exists : ∃qH : ℕ, 2 ≤ qH ∧ ∀q : ℕ, qH ≤ q →
    ∀(n m : ℕ) (G : MultiGraph n m), 0 < n → G.TreePackable univ q →
    ∀(R : Fin m → ℝ) (t : ℝ), 0 < t → ∃Y ∈ G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩
        G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card:ℝ) ≤
      16*((q:ℝ)^(-31/40:ℝ)/t+1/(q:ℝ)) *
        (G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card := by
  obtain ⟨qH,hqH,hshortcut⟩ := Hierarchy.polynomial_shortcut
  refine ⟨qH,hqH,?_⟩
  intro q hq n m G hn hpack R t ht
  have hqp : 0 < q := by omega
  let P := G.packingChain R q
  let I := insert m (Dyadic.selected (fun j => (P.crossing G j).card) m)
  have hroot : P.parts m={univ} := G.packingChain_root R hn hpack
  obtain ⟨H,hH⟩ := P.exists_hierarchy I ⟨m,mem_insert_self _ _,hroot ▸ mem_singleton_self _⟩
  have hlocal : H.LocallyConnectedReal G q := G.chain_locally P I H hH (fun i _ => G.packingChain_local R q i)
  let M := H.nodes.filter (fun A => A ≠ univ ∧ ((G.cut univ A).card:ℝ)/q ≤ (H.parentBoundary G A).card)
  obtain ⟨D,hD,hcut,havg⟩ := hshortcut q hq n m G H hlocal M (filter_subset _ _)
    (fun A hA => (mem_filter.mp hA).2.1) (fun A hA => (mem_filter.mp hA).2.2)
  have hc : G.EdgeConnected 1 := fun S hS hS' => (by omega : 1 ≤ q).trans (Hierarchy.edgeConnected_of_locally hlocal S hS hS')
  obtain ⟨Y,hYm,hnode⟩ := G.shortcut_response hqp hn hc (Real.rpow_nonneg (Nat.cast_nonneg q) _) ht D hD hcut
    (fun A hA hA' hr => havg A (mem_filter.mpr ⟨hA,hA',hr⟩))
  refine ⟨Y,hYm,fun s => ?_⟩
  have hz : (G.thresholdEdges R s).card ≤ m := by simpa using card_le_univ (G.thresholdEdges R s)
  have hh := P.simultaneous_bad_bound G hroot hH (univ.filter (fun e => t < G.resistance Y e))
    (by positivity : 0 ≤ (q:ℝ)^(-31/40:ℝ)/t+1/(q:ℝ)) hnode (G.thresholdEdges R s).card hz
  have heq : P.crossing G (G.thresholdEdges R s).card=G.crossing univ (G.partLabel (G.thresholdEdges R s) q) := by
    rw [G.packingChain_crossing,G.rankedEdges_threshold]
  simpa only [heq] using hh

end StrongThinTree.MultiGraph

end
end

end OAI
