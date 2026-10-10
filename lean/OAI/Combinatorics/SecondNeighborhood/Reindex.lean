import OAI.Combinatorics.SecondNeighborhood.ReductionCore
import Mathlib.Data.Fintype.EquivFin

namespace OAI

namespace SeymourSecondNeighborhood

variable {V W : Type*}

def reindex (e : V ≃ W) (r : V → V → Prop) : W → W → Prop :=
  fun x y => r (e.symm x) (e.symm y)

theorem isOriented_reindex (e : V ≃ W) {r : V → V → Prop}
    (hr : IsOriented r) : IsOriented (reindex e r) where
  loopless w := hr.loopless (e.symm w)
  asymmetric hxy hyx := hr.asymmetric hxy hyx

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem mem_firstNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (v w : W) :
    w ∈ firstNeighbors (reindex e r) v ↔
      e.symm w ∈ firstNeighbors r (e.symm v) := by
  simp only [mem_firstNeighbors, reindex]

@[simp] theorem mem_secondNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (v w : W) :
    w ∈ secondNeighbors (reindex e r) v ↔
      e.symm w ∈ secondNeighbors r (e.symm v) := by
  simp only [mem_secondNeighbors, reindex]
  constructor
  · rintro ⟨hneq, hnot, u, hvu, huw⟩
    exact ⟨fun heq => hneq (e.symm.injective heq), hnot, e.symm u, hvu, huw⟩
  · rintro ⟨hneq, hnot, u, hvu, huw⟩
    refine ⟨fun heq => hneq (congrArg e.symm heq), hnot, e u, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hvu
    · simpa only [Equiv.symm_apply_apply] using huw

omit [DecidableEq V] [DecidableEq W] in
theorem firstNeighbors_reindex (e : V ≃ W) (r : V → V → Prop) (w : W) :
    firstNeighbors (reindex e r) w =
      (firstNeighbors r (e.symm w)).map e.toEmbedding := by
  ext v
  simp only [Finset.mem_map_equiv, mem_firstNeighbors_reindex]

theorem secondNeighbors_reindex (e : V ≃ W) (r : V → V → Prop) (w : W) :
    secondNeighbors (reindex e r) w =
      (secondNeighbors r (e.symm w)).map e.toEmbedding := by
  ext v
  simp only [Finset.mem_map_equiv, mem_secondNeighbors_reindex]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem card_firstNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (w : W) :
    (firstNeighbors (reindex e r) w).card =
      (firstNeighbors r (e.symm w)).card := by
  rw [firstNeighbors_reindex, Finset.card_map]

@[simp] theorem card_secondNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (w : W) :
    (secondNeighbors (reindex e r) w).card =
      (secondNeighbors r (e.symm w)).card := by
  rw [secondNeighbors_reindex, Finset.card_map]

theorem counterexample_reindex (e : V ≃ W) {r : V → V → Prop}
    (h : Counterexample r) : Counterexample (reindex e r) := by
  intro w
  rw [card_secondNeighbors_reindex, card_firstNeighbors_reindex]
  exact h (e.symm w)

theorem counterexample_reindex_iff (e : V ≃ W) (r : V → V → Prop) :
    Counterexample (reindex e r) ↔ Counterexample r := by
  constructor
  · intro h v
    have hv := h (e v)
    simpa only [card_secondNeighbors_reindex, card_firstNeighbors_reindex,
      Equiv.symm_apply_apply] using hv
  · exact counterexample_reindex e

theorem exists_counterexample_fin {r : V → V → Prop}
    (hr : IsOriented r) (h : Counterexample r) :
    ∃ s : Fin (Fintype.card V) → Fin (Fintype.card V) → Prop,
      IsOriented s ∧ Counterexample s := by
  exact ⟨reindex (Fintype.equivFin V) r,
    isOriented_reindex (Fintype.equivFin V) hr,
    counterexample_reindex (Fintype.equivFin V) h⟩

end SeymourSecondNeighborhood

end OAI
