import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.OrientedEdges

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
open Classical in

theorem prefixEmbeddings_edge_cover {n N R : ℕ} (J : SimpleGraph (Fin N))
    (G : Graph n) (hG : ∀ e ∈ G, e.card = 2) (hR : R ≤ N)
    (E : Finset (Finset (Fin R))) (hE : ∀ e ∈ E, e.card = 2)
    (hcover : ∀ i : Fin R, ∃ e ∈ E, i ∈ e)
    (hedge : ∀ e ∈ E, ∀ x ∈ e, ∀ y ∈ e, x ≠ y →
      J.Adj (Fin.castLE hR x) (Fin.castLE hR y)) :
    (prefixEmbeddings J (lookupGraph G) R hR).card ≤ (2 * G.card)^E.card := by
  classical
  let e : Fin E.card ≃ ↥E := (Fin.castOrderIso (Fintype.card_coe E).symm).toEquiv.trans
    (Fintype.equivFin ↥E).symm
  have hh : ∀ j : Fin E.card, ∃ u v : Fin R, u ≠ v ∧ (e j).val = {u,v} := by
    intro j
    exact Finset.card_eq_two.mp (hE _ (e j).property)
  choose u v huv huvE using hh
  apply prefixEmbeddings_root_cover J G hG hR u v
  · intro i
    obtain ⟨f,hf,hif⟩ := hcover i
    let j := e.symm ⟨f,hf⟩
    have hej : (e j).val = f := congrArg Subtype.val (e.apply_symm_apply _)
    have hmem : i ∈ ({u j,v j} : Finset (Fin R)) := by rwa [← huvE j,hej]
    exact ⟨j,by simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem⟩
  · intro j
    exact hedge _ (e j).property _ (by rw [huvE j]; simp) _
      (by rw [huvE j]; simp) (huv j)

end SharpTerminalLeave

end

end OAI
