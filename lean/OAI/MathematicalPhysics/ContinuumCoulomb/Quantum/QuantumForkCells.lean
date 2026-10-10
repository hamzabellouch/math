import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkState

namespace OAI

/-! A fork round keeps each new pair in the coarse cell of its active center. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {n c : ℕ} {d : Fin c → ℕ} {β : Type*}

def qmaForkCellNext (P : QMAForkPorts n c d) (cell : Fin n → β) :
    Fin (n+P.pairCount*2) → β :=
  Sum.elim cell (fun p : Fin P.pairCount × Fin 2 => cell (P.center (P.pairEquiv.symm p.1).1)) ∘
    (vertexEquiv n P.pairCount).symm

@[simp] theorem qmaForkCellNext_old (P : QMAForkPorts n c d) (cell : Fin n → β) (v : Fin n) :
    qmaForkCellNext P cell (old n P.pairCount v) = cell v := by
  simp [qmaForkCellNext,old]

@[simp] theorem qmaForkCellNext_fresh (P : QMAForkPorts n c d) (cell : Fin n → β)
    (e : Fin P.pairCount) (b : Fin 2) :
    qmaForkCellNext P cell (fresh n P.pairCount e b) = cell (P.center (P.pairEquiv.symm e).1) := by
  simp [qmaForkCellNext,fresh]

def QMAForkCellAligned (P : QMAForkPorts n c d) (cell : Fin n → β) : Prop :=
  ∀ p, cell (P.port p) = cell (P.center p.1)

theorem qmaForkCellNext_aligned (P : QMAForkPorts n c d) (cell : Fin n → β)
    (h : QMAForkCellAligned P cell) : QMAForkCellAligned P.next (qmaForkCellNext P cell) := by
  intro p
  obtain ⟨p,rfl⟩ := P.nextPortEquiv.symm.surjective p
  rcases p with p | p
  · simp only [QMAForkPorts.next,Function.comp_apply,Equiv.apply_symm_apply,
      QMAForkPorts.nextPortAux,qmaForkCellNext_old,qmaForkCellNext_fresh,Equiv.symm_apply_apply]
    rfl
  · simp only [QMAForkPorts.next,Function.comp_apply,Equiv.apply_symm_apply,
      QMAForkPorts.nextPortAux,qmaForkCellNext_old]
    exact h (qmaForkRemainingPort d p)

def qmaCellMass {V : Type*} [Fintype V] [DecidableEq β] (cell : V → β) (x : β) : ℕ :=
  ∑ v, if cell v = x then 1 else 0

theorem qmaForkCellNext_mass [DecidableEq β] (P : QMAForkPorts n c d)
    (cell : Fin n → β) (x : β) :
    qmaCellMass (qmaForkCellNext P cell) x = qmaCellMass cell x +
      2*∑ e : Fin P.pairCount, if cell (P.center (P.pairEquiv.symm e).1) = x then 1 else 0 := by
  unfold qmaCellMass
  rw [← (vertexEquiv n P.pairCount).sum_comp]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [qmaForkCellNext,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  change (∑ v : Fin n, if cell v = x then 1 else 0) +
    (∑ e : Fin P.pairCount, ((if cell (P.center (P.pairEquiv.symm e).1) = x then 1 else 0) +
      (if cell (P.center (P.pairEquiv.symm e).1) = x then 1 else 0))) = _
  rw [Finset.sum_add_distrib]
  omega

theorem qmaForkCell_pair_mass_le [DecidableEq β] (P : QMAForkPorts n c d)
    (cell : Fin n → β) (D : ℕ) (hd : ∀ i, d i ≤ D) (x : β) :
    (∑ e : Fin P.pairCount, if cell (P.center (P.pairEquiv.symm e).1) = x then 1 else 0 : ℕ) ≤
      D*qmaCellMass (cell ∘ P.center) x := by
  have he := P.pairEquiv.symm.sum_comp (fun p : QMAForkPair d =>
    if cell (P.center p.1) = x then (1:ℕ) else 0)
  rw [he]
  simp only [Fintype.sum_sigma,qmaCellMass,Function.comp_apply,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : cell (P.center i) = x
  · simp only [hx,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,Nat.mul_one]
    exact (Nat.div_le_self _ _).trans (hd i)
  · simp [hx]

theorem qmaForkCellNext_mass_le [DecidableEq β] (P : QMAForkPorts n c d)
    (cell : Fin n → β) (D : ℕ) (hd : ∀ i, d i ≤ D) (x : β) :
    qmaCellMass (qmaForkCellNext P cell) x ≤ qmaCellMass cell x +
      2*D*qmaCellMass (cell ∘ P.center) x := by
  rw [qmaForkCellNext_mass]
  have h := qmaForkCell_pair_mass_le P cell D hd x
  calc
    _ ≤ qmaCellMass cell x+2*(D*qmaCellMass (cell ∘ P.center) x) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
