import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCells

namespace OAI

/-! Every new ordinary bond remains within its original coarse cell. Old
ordinary bonds retain their cells, so arbitrary reflexive locality relations
are preserved by the actual list transformation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def BondLocal {β : Type*} (bs : List Bond) (cell : ℕ → β) (R : β → β → Prop) : Prop :=
  ∀ b ∈ bs, R (cell b.1) (cell b.2.1)

theorem addedBonds_cellLocal {β : Type*} (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (cell : ℕ → β) (ha : CellAligned s cell) (R : β → β → Prop)
    (hr : ∀ x, R x x) (scale : ℚ) : BondLocal (addedBonds s scale) (nextCell s cell) R := by
  intro b hb
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' : i<pairCount s.2.2.2 := by
    simpa only [catalog_length] using List.mem_range.mp hi
  let e : Fin (pairCount s.2.2.2) := ⟨i,hi'⟩
  rw [catalog_actualSite hs e] at hb
  have hc (a : Fin 3) : nextCell s cell (actualSite hs e a).val=
      cell (actualSite hs e 0).val :=
    (nextCell_old s cell _ (actualSite hs e a).isLt).trans
      (cellAligned_actualSite s hs cell ha e a)
  have hf0 : nextCell s cell (s.1+2*i)=cell (actualSite hs e 0).val := by
    simpa only [Fin.val_zero,Nat.add_zero] using nextCell_fresh s hs cell e 0
  have hf1 : nextCell s cell (s.1+2*i+1)=cell (actualSite hs e 0).val := by
    simpa only [Fin.val_one] using nextCell_fresh s hs cell e 1
  simp only [pairBonds,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;>
    simpa only [hc,hf0,hf1] using hr (cell (actualSite hs e 0).val)

theorem next_cellLocal {β : Type*} (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (cell : ℕ → β) (ha : CellAligned s cell)
    (R : β → β → Prop) (hr : ∀ x, R x x) (hl : BondLocal s.2.1 cell R) :
    BondLocal (next N s).2.1 (nextCell s cell) R := by
  intro b hm
  change b ∈ s.2.1++addedBonds s (scale N s) at hm
  rcases List.mem_append.mp hm with ho | hn
  · rw [nextCell_old s cell _ (hb b ho).1,nextCell_old s cell _ (hb b ho).2]
    exact hl b ho
  · exact addedBonds_cellLocal s hs cell ha R hr (scale N s) b hn

def iterateCell {β : Type*} (N : ℚ) : ℕ → State → (ℕ → β) → ℕ → β
  | 0,_,cell => cell
  | k+1,s,cell => nextCell (iterate N k s) (iterateCell N k s cell)

theorem iterate_cellAligned {β : Type*} (N : ℚ) (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (cell : ℕ → β) (ha : CellAligned s cell) (k : ℕ) :
    CellAligned (iterate N k s) (iterateCell N k s cell) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact next_cellAligned N _ (iterate_validPorts N s hs k) _ ih

theorem iterate_cellLocal {β : Type*} (N : ℚ) (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (hb : SourceBondLists.bounded s.1 s.2.1)
    (cell : ℕ → β) (ha : CellAligned s cell) (R : β → β → Prop)
    (hr : ∀ x, R x x) (hl : BondLocal s.2.1 cell R) (k : ℕ) :
    BondLocal (iterate N k s).2.1 (iterateCell N k s cell) R := by
  induction k with
  | zero => exact hl
  | succ k ih =>
    exact next_cellLocal N _ (iterate_validPorts N s hs k)
      (iterate_ordinary_bounded N s hs hb k) _ (iterate_cellAligned N s hs cell ha k) R hr ih

end ContinuumCoulomb.QuantumForkList

end

end OAI
