import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireIntertwining

namespace OAI

/-! A logical gate may be inserted when its operands have reached the next row. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaRelabelGate_fixed (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (hg : g.WellFormed (work+1))
    (hs : ∀ i ∈ qmaGateSites work g, σ i = i) : qmaRelabelGate work σ g = g := by
  cases g with
  | hadamard i =>
    have hi := hs (qmaQubit work i) (by simp [qmaGateSites])
    rw [qmaRelabelGate,hi]
    simp only [qmaQubit,Nat.mod_eq_of_lt hg]
  | phaseT i =>
    have hi := hs (qmaQubit work i) (by simp [qmaGateSites])
    rw [qmaRelabelGate,hi]
    simp only [qmaQubit,Nat.mod_eq_of_lt hg]
  | controlledNot i j =>
    have hi := hs (qmaQubit work i) (by simp [qmaGateSites])
    have hj := hs (qmaQubit work j) (by simp [qmaGateSites])
    rw [qmaRelabelGate,hi,hj]
    simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1]

theorem qmaTransferGates_append {work : ℕ}
    (xs ys : List (Fin (work+1) × Fin (work+1))) :
    qmaTransferGates (xs++ys) = qmaTransferGates xs++qmaTransferGates ys := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨i,j⟩
    simp only [List.cons_append,qmaTransferGates,ih,List.append_assoc]

theorem qmaTransfer_gate_commute {work : ℕ}
    (ps : List (Fin (work+1) × Fin (work+1))) (hp : ∀ p ∈ ps, p.1 ≠ p.2)
    (g : QMAGate) (hg : g.WellFormed (work+1))
    (ha : ∀ i ∈ qmaGateSites work g, ∀ p ∈ ps, i ≠ p.1 ∧ i ≠ p.2) :
    qmaGateProduct work (qmaTransferGates ps)*qmaGateMatrix work g =
      qmaGateMatrix work g*qmaGateProduct work (qmaTransferGates ps) := by
  let σ := qmaTransferPermutation ps
  have hs : ∀ i ∈ qmaGateSites work g, σ i = i :=
    fun i hi => qmaTransferPermutation_fixed ps i (ha i hi)
  have hi : ∀ i ∈ qmaGateSites work g, σ.symm i = i := by
    intro i h
    exact σ.symm_apply_eq.mpr (hs i h).symm
  rw [qmaTransferGates_matrix ps hp]
  change qmaWirePermutation (qmaWireBasis σ)*qmaGateMatrix work g =
    qmaGateMatrix work g*qmaWirePermutation (qmaWireBasis σ)
  rw [qmaGate_wire_intertwines,qmaRelabelGate_fixed work σ.symm g hg hi]

theorem qmaTransfer_insert_gate {work : ℕ}
    (xs ys : List (Fin (work+1) × Fin (work+1))) (hy : ∀ p ∈ ys, p.1 ≠ p.2)
    (g : QMAGate) (hg : g.WellFormed (work+1))
    (ha : ∀ i ∈ qmaGateSites work g, ∀ p ∈ ys, i ≠ p.1 ∧ i ≠ p.2) :
    qmaGateProduct work (qmaTransferGates xs++[g]++qmaTransferGates ys) =
      qmaGateMatrix work g*qmaGateProduct work (qmaTransferGates (xs++ys)) := by
  simp only [qmaTransferGates_append,qmaGateProduct_append,qmaGateProduct_singleton]
  rw [←mul_assoc,qmaTransfer_gate_commute ys hy g hg ha,mul_assoc]

end ContinuumCoulomb

end

end OAI
