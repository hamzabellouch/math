import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFirstUse

namespace OAI

/-! Moving a complete register between two disjoint rows. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaRowPairs {n work : ℕ} (l r : Fin n → Fin (work+1)) :
    List (Fin (work+1) × Fin (work+1)) := List.ofFn (fun i => (l i,r i))

theorem qmaRowPairs_disjoint {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) : (qmaRowPairs l r).Pairwise QMATransferDisjoint := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  have hne : i ≠ j := ne_of_lt hij
  exact ⟨fun h => hne (hl h),hlr i j,(hlr j i).symm,fun h => hne (hr h)⟩

theorem qmaRowPairs_distinct {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hlr : ∀ i j, l i ≠ r j) : ∀ p ∈ qmaRowPairs l r, p.1 ≠ p.2 := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact hlr i i

theorem qmaRowTransfer_coordinates {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (i : Fin n) :
    qmaTransferPermutation (qmaRowPairs l r) (l i) = r i ∧
      qmaTransferPermutation (qmaRowPairs l r) (r i) = l i :=
  qmaTransferPermutation_exchanges _ (qmaRowPairs_disjoint l r hl hr hlr) (l i,r i)
    (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem qmaRowTransfer_fixed {n work : ℕ} (l r : Fin n → Fin (work+1))
    (k : Fin (work+1)) (hl : ∀ i, k ≠ l i) (hr : ∀ i, k ≠ r i) :
    qmaTransferPermutation (qmaRowPairs l r) k = k := by
  apply qmaTransferPermutation_fixed
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨hl i,hr i⟩

theorem qmaRowTransfer_involutive {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) :
    Function.Involutive (qmaTransferPermutation (qmaRowPairs l r)) := by
  intro k
  by_cases hleft : ∃ i, k = l i
  · obtain ⟨i,rfl⟩ := hleft
    rw [(qmaRowTransfer_coordinates l r hl hr hlr i).1,
      (qmaRowTransfer_coordinates l r hl hr hlr i).2]
  by_cases hright : ∃ i, k = r i
  · obtain ⟨i,rfl⟩ := hright
    rw [(qmaRowTransfer_coordinates l r hl hr hlr i).2,
      (qmaRowTransfer_coordinates l r hl hr hlr i).1]
  · have h := qmaRowTransfer_fixed l r k
      (fun i hi => hleft ⟨i,hi⟩) (fun i hi => hright ⟨i,hi⟩)
    rw [h,h]

theorem qmaRowTransfer_matrix {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hlr : ∀ i j, l i ≠ r j) :
    qmaGateProduct work (qmaTransferGates (qmaRowPairs l r)) =
      qmaWirePermutation (fun s => s ∘ qmaTransferPermutation (qmaRowPairs l r)) :=
  qmaTransferGates_matrix _ (qmaRowPairs_distinct l r hlr)

theorem qmaRowTransfer_length {n work : ℕ} (l r : Fin n → Fin (work+1)) :
    (qmaTransferGates (qmaRowPairs l r)).length = 3*n := by
  simp [qmaTransferGates_length,qmaRowPairs]

end ContinuumCoulomb

end

end OAI
