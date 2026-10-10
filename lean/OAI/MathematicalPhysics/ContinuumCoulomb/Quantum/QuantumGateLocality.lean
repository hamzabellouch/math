import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalTensor

namespace OAI

/-! The fixed verifier gates act on at most two actual qubits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGateSites (work : ℕ) : QMAGate → Finset (Fin (work+1))
  | .hadamard i => {qmaQubit work i}
  | .phaseT i => {qmaQubit work i}
  | .controlledNot i j => {qmaQubit work i,qmaQubit work j}

theorem qmaGateSites_card (work : ℕ) (g : QMAGate) : (qmaGateSites work g).card ≤ 2 := by
  cases g with
  | hadamard i => simp [qmaGateSites]
  | phaseT i => simp [qmaGateSites]
  | controlledNot i j =>
    by_cases h : qmaQubit work i = qmaQubit work j
    · simp [qmaGateSites,h]
    · simp [qmaGateSites,h]

theorem qmaGateMatrix_local (work : ℕ) (g : QMAGate) :
    QMALocalOn (qmaGateSites work g) (qmaGateMatrix work g) := by
  cases g with
  | hadamard i =>
    apply qmaLocalOn_sourceTensor
    intro k hk
    exact ite_eq_right (by simpa only [qmaGateSites,Finset.mem_singleton] using hk)
  | phaseT i =>
    apply qmaLocalOn_sourceTensor
    intro k hk
    exact ite_eq_right (by simpa only [qmaGateSites,Finset.mem_singleton] using hk)
  | controlledNot i j =>
    let S := qmaGateSites work (.controlledNot i j)
    let ci : {k // k ∈ S} := ⟨qmaQubit work i,by simp [S,qmaGateSites]⟩
    let f : QMASupportBasis S → QMASupportBasis S := fun s k =>
      if k.val = qmaQubit work j ∧ s ci = 1 then Equiv.swap (0:Fin 2) 1 (s k) else s k
    apply qmaLocalOn_permutation S (qmaControlledNot work (qmaQubit work i) (qmaQubit work j)) f
    · intro t
      funext k
      rfl
    · intro t
      funext k
      have hk : k.val ≠ qmaQubit work j := by
        have h := k.property
        simp only [S,qmaGateSites,Finset.mem_insert,Finset.mem_singleton,not_or] at h
        exact h.2
      simp [qmaSupportSplit,Equiv.piEquivPiSubtypeProd,qmaControlledNot,hk]

end ContinuumCoulomb

end

end OAI
