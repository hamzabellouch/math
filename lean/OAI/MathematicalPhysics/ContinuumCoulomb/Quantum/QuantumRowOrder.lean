import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridAcceptance

namespace OAI

/-! The completed row transfer is independent of the chosen column order. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaRowTransfer_reindex {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin n)) :
    qmaTransferPermutation (qmaRowPairs (l ∘ e) (r ∘ e)) =
      qmaTransferPermutation (qmaRowPairs l r) := by
  have hl' : Function.Injective (l ∘ e) := hl.comp e.injective
  have hr' : Function.Injective (r ∘ e) := hr.comp e.injective
  have hlr' : ∀ i j, (l ∘ e) i ≠ (r ∘ e) j := fun i j => hlr (e i) (e j)
  apply Equiv.ext
  intro k
  by_cases hleft : ∃ i, k = l i
  · obtain ⟨i,rfl⟩ := hleft
    have ht := (qmaRowTransfer_coordinates (l ∘ e) (r ∘ e) hl' hr' hlr' (e.symm i)).1
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,
      (qmaRowTransfer_coordinates l r hl hr hlr i).1] using ht
  by_cases hright : ∃ i, k = r i
  · obtain ⟨i,rfl⟩ := hright
    have ht := (qmaRowTransfer_coordinates (l ∘ e) (r ∘ e) hl' hr' hlr' (e.symm i)).2
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,
      (qmaRowTransfer_coordinates l r hl hr hlr i).2] using ht
  · rw [qmaRowTransfer_fixed (l ∘ e) (r ∘ e) k
      (fun i hi => hleft ⟨e i,hi⟩) (fun i hi => hright ⟨e i,hi⟩),
      qmaRowTransfer_fixed l r k (fun i hi => hleft ⟨i,hi⟩) (fun i hi => hright ⟨i,hi⟩)]

theorem qmaRowTransfer_matrix_reindex {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin n)) :
    qmaGateProduct work (qmaTransferGates (qmaRowPairs (l ∘ e) (r ∘ e))) =
      qmaGateProduct work (qmaTransferGates (qmaRowPairs l r)) := by
  rw [qmaRowTransfer_matrix (l ∘ e) (r ∘ e) (fun i j => hlr (e i) (e j)),
    qmaRowTransfer_matrix l r hlr,qmaRowTransfer_reindex l r hl hr hlr e]

end ContinuumCoulomb

end

end OAI
