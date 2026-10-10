import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialCellMass

namespace OAI

/-! The full emitted bond list, including active ports, keeps the original
common-cell locality relation through initial subdivision and all fork rounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

theorem activeBonds_mem {gs : Groups} {b : Bond} (hb : b ∈ activeBonds gs) :
    ∃ (i : Fin gs.length) (j : Fin (groupAt gs i.val).length),
      b=(i.val,(portAt (groupAt gs i.val) j.val).1,
        (portAt (groupAt gs i.val) j.val).2) := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  obtain ⟨j,hj⟩ := List.get_of_mem hp
  refine ⟨⟨i,List.mem_range.mp hi⟩,j,?_⟩
  have he : portAt (groupAt gs i) j.val=p := by
    rw [portAt_eq_getElem _ _ j.isLt]
    exact hj
  rw [he]

theorem activeBonds_valid {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (b : Bond) (hb : b ∈ activeBonds gs) :
    b.1<n ∧ b.2.1<n ∧ b.1≠b.2.1 := by
  obtain ⟨i,j,rfl⟩ := activeBonds_mem hb
  exact ⟨lt_of_lt_of_le i.isLt h.centers,h.bounded i j,h.disjoint i i j⟩

theorem activeBonds_cellLocal {β : Type*} (s : State) (cell : ℕ → β)
    (ha : CellAligned s cell) (R : β → β → Prop) (hr : ∀ x, R x x) :
    BondLocal (activeBonds s.2.2.2) cell R := by
  intro b hb
  obtain ⟨i,j,rfl⟩ := activeBonds_mem hb
  change R (cell i.val) (cell (portAt (groupAt s.2.2.2 i.val) j.val).1)
  rw [ha i j]
  exact hr _

theorem full_cellLocal {β : Type*} (s : State) (cell : ℕ → β)
    (ha : CellAligned s cell) (R : β → β → Prop) (hr : ∀ x, R x x)
    (hl : BondLocal s.2.1 cell R) :
    BondLocal (s.2.1++activeBonds s.2.2.2) cell R := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hl b hb
  · exact activeBonds_cellLocal s cell ha R hr b hb

theorem initial_iterate_full_cellLocal {β : Type*} (n : ℕ) (bs : List Bond)
    (c N : ℚ) (cell : ℕ → β) (R : β → β → Prop) (hr : ∀ x, R x x)
    (hl : BondLocal bs cell R) (k : ℕ) :
    BondLocal ((iterate N k (initial n bs c N)).2.1++
      activeBonds (iterate N k (initial n bs c N)).2.2.2)
      (iterateCell N k (initial n bs c N) (initialCell n bs cell)) R := by
  apply full_cellLocal
  · exact iterate_cellAligned N _ (initial_validPorts n bs c N) _
      (initial_cellAligned n bs c N cell) k
  · exact hr
  · exact iterate_cellLocal N _ (initial_validPorts n bs c N)
      (initial_ordinary_bounded n bs c N) _ (initial_cellAligned n bs c N cell)
      R hr (initial_cellLocal n bs c N cell R hl) k

end ContinuumCoulomb.QuantumForkList

end

end OAI
