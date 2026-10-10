import OAI.Combinatorics.Ryser.Hypergraph.Definitions
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

namespace OAI

namespace RyserCoveringCounterexample

variable {V I J : Type*} [instDecidableEqV : DecidableEq V]

theorem PartiteUniform.edgePart_bijective {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) {e : Finset V} (he : e ∈ H) :
    Function.Bijective (fun v : ↥e => part v.val) := let _ := instDecidableEqV; by
  constructor
  · intro v w hvw
    apply Subtype.ext
    exact (hpart e he (part v.val)).unique
      ⟨v.property, rfl⟩ ⟨w.property, hvw.symm⟩
  · intro i
    obtain ⟨v, hve, hvi⟩ := (hpart e he i).exists
    exact ⟨⟨v, hve⟩, hvi⟩

theorem PartiteUniform.edge_card [Fintype I] {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) {e : Finset V} (he : e ∈ H) :
    e.card = Fintype.card I := by
  exact (Fintype.card_coe e).symm.trans
    (Fintype.card_of_bijective (hpart.edgePart_bijective he))

theorem PartiteUniform.uniform [Fintype I] {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) : Uniform (Fintype.card I) H := by
  intro e he
  exact hpart.edge_card he

theorem RPartiteUniform.uniform {r : ℕ} {H : Hypergraph V}
    (hpart : RPartiteUniform r H) : Uniform r H := by
  obtain ⟨part, hpart⟩ := hpart
  intro e he
  simpa only [Fintype.card_fin] using hpart.edge_card he

theorem Uniform.nonemptyEdges {r : ℕ} {H : Hypergraph V}
    (huniform : Uniform r H) (hr : 0 < r) : NonemptyEdges H := let _ := instDecidableEqV; by
  intro e he
  apply Finset.card_pos.mp
  rw [huniform e he]
  exact hr

theorem RPartiteUniform.nonemptyEdges {r : ℕ} {H : Hypergraph V}
    (hpart : RPartiteUniform r H) (hr : 0 < r) : NonemptyEdges H :=
  hpart.uniform.nonemptyEdges hr

theorem PartiteUniform.relabel {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) (f : I ≃ J) :
    PartiteUniform (f ∘ part) H := let _ := instDecidableEqV; by
  intro e he j
  obtain ⟨v, hv, huniq⟩ := hpart e he (f.symm j)
  refine ⟨v, ⟨hv.1, ?_⟩, ?_⟩
  · change f (part v) = j
    rw [hv.2, f.apply_symm_apply]
  · intro w hw
    apply huniq w
    refine ⟨hw.1, ?_⟩
    exact f.injective (hw.2.trans (f.apply_symm_apply j).symm)

theorem PartiteUniform.rPartiteUniform [Fintype I] {part : V → I}
    {H : Hypergraph V} (hpart : PartiteUniform part H) :
    RPartiteUniform (Fintype.card I) H := by
  refine ⟨(Fintype.equivFin I) ∘ part, ?_⟩
  exact hpart.relabel (Fintype.equivFin I)

end RyserCoveringCounterexample

end OAI
