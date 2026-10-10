import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumQuadratic

namespace OAI

/-! Finite clock coordinates and their exact Euclidean mass. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

abbrev QMAHistoryBasis (c : QMACircuit) :=
  Fin (c.gates.length+1) × SourceSpinBasis (c.work+1)

def qmaClockIndex (c : QMACircuit) (t : ℕ) : Fin (c.gates.length+1) :=
  ⟨min t c.gates.length,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def qmaHistoryFromVector (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : ℕ) : EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  WithLp.toLp 2 (fun s => u (qmaClockIndex c t,s))

@[simp] theorem qmaClockIndex_fin (c : QMACircuit) (t : Fin (c.gates.length+1)) :
    qmaClockIndex c t.val = t := by
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ t.isLt)

@[simp] theorem qmaHistoryFromVector_fin (c : QMACircuit)
    (u : QMAHistoryBasis c → ℂ) (t : Fin (c.gates.length+1)) (s : SourceSpinBasis (c.work+1)) :
    qmaHistoryFromVector c u t.val s = u (t,s) := by
  simp [qmaHistoryFromVector]

theorem qmaHistoryFromVector_mass (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaHistoryMass c (qmaHistoryFromVector c u) = ‖WithLp.toLp 2 u‖^2 := by
  unfold qmaHistoryMass
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [EuclideanSpace.norm_sq_eq,qmaHistoryFromVector_fin]
  rw [Fintype.sum_prod_type]

end ContinuumCoulomb

end

end OAI
