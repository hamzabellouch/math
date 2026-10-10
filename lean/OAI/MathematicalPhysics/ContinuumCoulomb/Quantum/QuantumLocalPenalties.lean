import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalPropagation

namespace OAI

/-! The clock and endpoint penalties are explicit one- and two-qubit terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaBitDiagonal (i : ι) (f : Fin 2 → ℂ) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  Matrix.diagonal (fun s => f (s i))

def qmaPairDiagonal (i j : ι) (f : Fin 2 → Fin 2 → ℂ) :
    Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  Matrix.diagonal (fun s => f (s i) (s j))

theorem qmaBitDiagonal_local (i : ι) (f : Fin 2 → ℂ) :
    QMALocalOn {i} (qmaBitDiagonal i f) := by
  apply qmaLocalOn_diagonal
  intro s t h
  rw [h i (by simp)]

theorem qmaPairDiagonal_local (i j : ι) (f : Fin 2 → Fin 2 → ℂ) :
    QMALocalOn {i,j} (qmaPairDiagonal i j f) := by
  apply qmaLocalOn_diagonal
  intro s t h
  rw [h i (by simp),h j (by simp)]

def qmaClockFaultTerm (c : QMACircuit) (i : Fin (c.gates.length+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaPairDiagonal (Sum.inl i.castSucc) (Sum.inl i.succ)
    (fun a b => if a = 0 ∧ b = 1 then 1 else 0)

def qmaClockLeftTerm (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaBitDiagonal (Sum.inl 0) (fun a => if a = 1 then 0 else 1)

def qmaClockRightTerm (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaBitDiagonal (Sum.inl (Fin.last (c.gates.length+1))) (fun a => if a = 0 then 0 else 1)

def qmaInputTerm (c : QMACircuit) (i : Fin (c.work+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaPairDiagonal (Sum.inl (qmaInputMarker c)) (Sum.inr i)
    (fun a b => if a = 0 then if c.witness ≤ i.val ∧ b ≠ 0 then 7 else 0 else 0)

def qmaOutputTerm (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaPairDiagonal (Sum.inl (qmaOutputMarker c)) (Sum.inr (Fin.last c.work))
    (fun a b => if a = 1 ∧ b ≠ 1 then 1 else 0)

theorem qmaClockFaultTerm_local (c : QMACircuit) (i : Fin (c.gates.length+1)) :
    QMALocalOn {Sum.inl i.castSucc,Sum.inl i.succ} (qmaClockFaultTerm c i) :=
  qmaPairDiagonal_local _ _ _

theorem qmaClockLeftTerm_local (c : QMACircuit) :
    QMALocalOn {Sum.inl 0} (qmaClockLeftTerm c) := qmaBitDiagonal_local _ _

theorem qmaClockRightTerm_local (c : QMACircuit) :
    QMALocalOn {Sum.inl (Fin.last (c.gates.length+1))} (qmaClockRightTerm c) :=
  qmaBitDiagonal_local _ _

theorem qmaInputTerm_local (c : QMACircuit) (i : Fin (c.work+1)) :
    QMALocalOn {Sum.inl (qmaInputMarker c),Sum.inr i} (qmaInputTerm c i) :=
  qmaPairDiagonal_local _ _ _

theorem qmaOutputTerm_local (c : QMACircuit) :
    QMALocalOn {Sum.inl (qmaOutputMarker c),Sum.inr (Fin.last c.work)} (qmaOutputTerm c) :=
  qmaPairDiagonal_local _ _ _

end ContinuumCoulomb

end

end OAI
