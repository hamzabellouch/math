import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkPlaced
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitial

namespace OAI

/-! Initial private ports and all subsequent fork vertices retain bounded cell density. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {n m : ℕ} {β : Type*}

theorem qmaOriginalPortEquiv_endpoint (left right : Fin m → Fin n)
    (p : Σ i, Fin (qmaOriginalPortCount left right i)) :
    qmaOriginalEndpoint left right (qmaOriginalPortEquiv left right p) = p.1 :=
  ((Fintype.equivFin {q : Fin m × Fin 2 // qmaOriginalEndpoint left right q = p.1}).symm p.2).property

def qmaSubdivisionCell (left right : Fin m → Fin n) (cell : Fin n → β) : Fin (n+m*2) → β :=
  Sum.elim cell (fun p => cell (qmaOriginalEndpoint left right p)) ∘ (vertexEquiv n m).symm

@[simp] theorem qmaSubdivisionCell_old (left right : Fin m → Fin n) (cell : Fin n → β)
    (i : Fin n) : qmaSubdivisionCell left right cell (old n m i) = cell i := by
  simp [qmaSubdivisionCell,old]

@[simp] theorem qmaSubdivisionCell_fresh (left right : Fin m → Fin n) (cell : Fin n → β)
    (e : Fin m) (b : Fin 2) :
    qmaSubdivisionCell left right cell (fresh n m e b) = cell (qmaOriginalEndpoint left right (e,b)) := by
  simp [qmaSubdivisionCell,fresh]

theorem qmaSubdivisionCell_aligned (left right : Fin m → Fin n) (cell : Fin n → β) :
    QMAForkCellAligned (qmaSubdivisionPorts left right) (qmaSubdivisionCell left right cell) := by
  intro p
  change qmaSubdivisionCell left right cell (fresh n m (qmaOriginalPortEquiv left right p).1
    (qmaOriginalPortEquiv left right p).2) = qmaSubdivisionCell left right cell (old n m p.1)
  rw [qmaSubdivisionCell_fresh,qmaSubdivisionCell_old]
  exact congrArg cell (qmaOriginalPortEquiv_endpoint left right p)

theorem qmaSubdivisionCell_mass [DecidableEq β] (left right : Fin m → Fin n)
    (cell : Fin n → β) (x : β) :
    qmaCellMass (qmaSubdivisionCell left right cell) x = qmaCellMass cell x +
      ∑ p : Fin m × Fin 2, if cell (qmaOriginalEndpoint left right p) = x then 1 else 0 := by
  unfold qmaCellMass
  rw [← (vertexEquiv n m).sum_comp,Fintype.sum_sum_type]
  simp only [qmaSubdivisionCell,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]

theorem qmaSubdivisionCell_mass_le [DecidableEq β] (left right : Fin m → Fin n)
    (cell : Fin n → β) (D : ℕ) (hd : ∀ i, qmaOriginalPortCount left right i ≤ D) (x : β) :
    qmaCellMass (qmaSubdivisionCell left right cell) x ≤ (D+1)*qmaCellMass cell x := by
  rw [qmaSubdivisionCell_mass]
  have hs := (qmaOriginalPortEquiv left right).sum_comp
    (fun p => if cell (qmaOriginalEndpoint left right p) = x then (1:ℕ) else 0)
  simp only [qmaOriginalPortEquiv_endpoint,Fintype.sum_sigma] at hs
  have hb : (∑ i : Fin n, ∑ _j : Fin (qmaOriginalPortCount left right i),
      if cell i = x then (1:ℕ) else 0) ≤ D*qmaCellMass cell x := by
    unfold qmaCellMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hx : cell i = x
    · simpa only [hx,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        smul_eq_mul,Nat.mul_one] using hd i
    · simp [hx]
  rw [← hs]
  calc
    _ ≤ qmaCellMass cell x+D*qmaCellMass cell x := Nat.add_le_add_left hb _
    _ = _ := by ring

def qmaSubdivisionPlaced (left right : Fin m → Fin n) (cell : Fin n → β) :
    QMAPlacedForkNetwork β n where
  graph := qmaSubdivisionNetwork left right
  cell := qmaSubdivisionCell left right cell
  aligned := qmaSubdivisionCell_aligned left right cell

theorem qmaSubdivisionPlaced_centerCell (left right : Fin m → Fin n) (cell : Fin n → β) :
    (qmaSubdivisionPlaced left right cell).centerCell = cell := by
  funext i
  exact qmaSubdivisionCell_old left right cell i

theorem qmaSubdivisionPlaced_density [DecidableEq β] (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (cell : Fin n → β) (D : ℕ)
    (hd : ∀ i, qmaGraphDegree left right i ≤ D) (x : β) :
    qmaCellMass ((qmaSubdivisionPlaced left right cell).iterate D).cell x ≤
      (1+D+2*D^2)*qmaCellMass cell x := by
  have hc : ∀ i, qmaOriginalPortCount left right i ≤ D := fun i =>
    (qmaOriginalPortCount_eq_degree left right hneq i).le.trans (hd i)
  have hi := (qmaSubdivisionPlaced left right cell).iterate_cell_mass D hc D x
  rw [qmaSubdivisionPlaced_centerCell] at hi
  have h0 := qmaSubdivisionCell_mass_le left right cell D hc x
  calc
    _ ≤ qmaCellMass (qmaSubdivisionCell left right cell) x+2*D*D*qmaCellMass cell x := hi
    _ ≤ (D+1)*qmaCellMass cell x+2*D*D*qmaCellMass cell x := Nat.add_le_add_right h0 _
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
