import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCellMass
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitialCells

namespace OAI

/-! The literal initial cell array has the original endpoint multiplicities.
Together with fixed fork rounds this gives a constant coarse-cell density. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph MediatorListProgram
open scoped BigOperators Classical
variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
theorem initialCell_eq_subdivision (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (cell : ℕ → β) (v : Fin (n+bs.length*2)) :
    initialCell n bs cell v.val=
      qmaSubdivisionCell (SourceBondLists.bonds n bs hb).left
        (SourceBondLists.bonds n bs hb).right (fun i => cell i.val) v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv n bs.length).surjective v
  rcases v with i | ⟨e,b⟩
  · change initialCell n bs cell (old n bs.length i).val=_
    rw [MediatorIteration.old_val,initialCell_old n bs cell i.val i.isLt]
    exact (qmaSubdivisionCell_old (SourceBondLists.bonds n bs hb).left
      (SourceBondLists.bonds n bs hb).right (fun j => cell j.val) i).symm
  · change initialCell n bs cell (fresh n bs.length e b).val=_
    refine Eq.trans ?_ (qmaSubdivisionCell_fresh
      (SourceBondLists.bonds n bs hb).left (SourceBondLists.bonds n bs hb).right
      (fun j => cell j.val) e b).symm
    rw [MediatorIteration.fresh_val]
    fin_cases b
    · simp only [Nat.add_zero]
      rw [initialCell_new,initialEndpoint_even]
      rfl
    · rw [Nat.add_assoc,initialCell_new,initialEndpoint_odd]
      rfl

theorem initial_cell_mass_le (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ b ∈ bs, b.1 ≠ b.2.1)
    (c N : ℚ) (cell : ℕ → β) (D : ℕ) (hd : ∀ i : Fin n, degree bs i.val ≤ D) (p : β) :
    qmaCellMass (fun v : Fin (initial n bs c N).1 => initialCell n bs cell v.val) p ≤
      (D+1)*qmaCellMass (fun v : Fin n => cell v.val) p := by
  change qmaCellMass (fun v : Fin (n+2*bs.length) => initialCell n bs cell v.val) p ≤ _
  rw [show n+2*bs.length=n+bs.length*2 by omega]
  have he : (fun v : Fin (n+bs.length*2) => initialCell n bs cell v.val)=
      qmaSubdivisionCell (SourceBondLists.bonds n bs hb).left
        (SourceBondLists.bonds n bs hb).right (fun v => cell v.val) :=
    funext (initialCell_eq_subdivision n bs hb cell)
  rw [he]
  apply qmaSubdivisionCell_mass_le
  intro i
  rw [qmaOriginalPortCount_eq_degree _ _ (SourceBondLists.bonds_noLoops n bs hb hn),
    ← degree_eq_graph]
  exact hd i

theorem initial_iterate_cell_mass_le (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ b ∈ bs, b.1 ≠ b.2.1)
    (c N : ℚ) (cell : ℕ → β) (D : ℕ) (hd : ∀ i : Fin n, degree bs i.val ≤ D)
    (k : ℕ) (p : β) :
    qmaCellMass (fun v : Fin (iterate N k (initial n bs c N)).1 =>
      iterateCell N k (initial n bs c N) (initialCell n bs cell) v.val) p ≤
        ((1+2*D)^k*(D+1))*qmaCellMass (fun v : Fin n => cell v.val) p := by
  have hg : ∀ i : Fin (initial n bs c N).2.2.2.length,
      (groupAt (initial n bs c N).2.2.2 i.val).length ≤ D := by
    intro i
    have hi : i.val<n := by simpa only [initial,List.length_map,List.length_range] using i.isLt
    change (groupAt ((List.range n).map (initialGroup n bs (initialScale N bs c))) i.val).length ≤ D
    rw [initial_groupAt _ _ _ _ hi]
    simp only [initialGroup,List.length_map,initialIndices_length_eq_degree bs hn]
    exact hd ⟨i.val,hi⟩
  have h := iterate_cell_mass_le (initial n bs c N) (initial_validPorts n bs c N) N
    (initialCell n bs cell) D hg k p
  calc
    _ ≤ (1+2*D)^k*qmaCellMass
        (fun v : Fin (initial n bs c N).1 => initialCell n bs cell v.val) p := h
    _ ≤ (1+2*D)^k*((D+1)*qmaCellMass (fun v : Fin n => cell v.val) p) :=
      Nat.mul_le_mul_left _ (initial_cell_mass_le n bs hb hn c N cell D hd p)
    _ = _ := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
