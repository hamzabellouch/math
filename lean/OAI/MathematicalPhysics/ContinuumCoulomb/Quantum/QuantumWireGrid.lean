import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTransferGate

namespace OAI

/-! Concrete row-major physical qubits for the space-time wire construction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev qmaGridWork (rows width : ℕ) : ℕ := width+rows*(width+1)

def qmaGridQubit (rows width : ℕ) (r : Fin (rows+1)) (i : Fin (width+1)) :
    Fin (qmaGridWork rows width+1) :=
  ⟨r.val*(width+1)+i.val,by
    have hr : r.val ≤ rows := Nat.le_of_lt_succ r.isLt
    have hi : i.val ≤ width := Nat.le_of_lt_succ i.isLt
    have hm := Nat.mul_le_mul_right (width+1) hr
    unfold qmaGridWork
    omega⟩

theorem qmaGridQubit_injective (rows width : ℕ) :
    Function.Injective (fun p : Fin (rows+1) × Fin (width+1) => qmaGridQubit rows width p.1 p.2) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  have hv : r.val*(width+1)+i.val = s.val*(width+1)+j.val := congrArg Fin.val h
  have hm := congrArg (fun k => k % (width+1)) hv
  rw [Nat.mul_add_mod_self_right,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hm
  have hi : i = j := Fin.ext hm
  have hr : r = s := by
    apply Fin.ext
    have hpos : 0 < width+1 := by omega
    have hij : i.val = j.val := congrArg Fin.val hi
    nlinarith
  exact Prod.ext hr hi

theorem qmaGridRow_injective (rows width : ℕ) (r : Fin (rows+1)) :
    Function.Injective (qmaGridQubit rows width r) := by
  intro i j h
  exact congrArg Prod.snd (qmaGridQubit_injective rows width (a₁ := (r,i)) (a₂ := (r,j)) h)

theorem qmaGridRows_disjoint (rows width : ℕ) (r s : Fin (rows+1)) (hrs : r ≠ s)
    (i j : Fin (width+1)) : qmaGridQubit rows width r i ≠ qmaGridQubit rows width s j := by
  intro h
  exact hrs (congrArg Prod.fst (qmaGridQubit_injective rows width (a₁ := (r,i)) (a₂ := (s,j)) h))

def qmaGridTransfer (rows width : ℕ) (r : Fin rows) : List QMAGate :=
  qmaTransferGates (qmaRowPairs (qmaGridQubit rows width r.castSucc)
    (qmaGridQubit rows width r.succ))

theorem qmaGridTransfer_length (rows width : ℕ) (r : Fin rows) :
    (qmaGridTransfer rows width r).length = 3*(width+1) := qmaRowTransfer_length _ _

theorem qmaGridRow_ne (rows : ℕ) (r : Fin rows) : r.castSucc ≠ r.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

theorem qmaGridTransfer_wellFormed (rows width : ℕ) (r : Fin rows) :
    ∀ g ∈ qmaGridTransfer rows width r, g.WellFormed (qmaGridWork rows width+1) := by
  apply qmaTransferGates_wellFormed
  apply qmaRowPairs_distinct
  exact qmaGridRows_disjoint rows width r.castSucc r.succ (qmaGridRow_ne rows r)

theorem qmaGridTransfer_coordinates (rows width : ℕ) (r : Fin rows) (i : Fin (width+1)) :
    let σ := qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ))
    σ (qmaGridQubit rows width r.castSucc i) = qmaGridQubit rows width r.succ i ∧
      σ (qmaGridQubit rows width r.succ i) = qmaGridQubit rows width r.castSucc i := by
  exact qmaRowTransfer_coordinates _ _ (qmaGridRow_injective rows width r.castSucc)
    (qmaGridRow_injective rows width r.succ)
    (qmaGridRows_disjoint rows width r.castSucc r.succ (qmaGridRow_ne rows r)) i

end ContinuumCoulomb

end

end OAI
