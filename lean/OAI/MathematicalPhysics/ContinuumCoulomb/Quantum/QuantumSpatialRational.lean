import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialXZBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliRounding

namespace OAI

/-! Rational coefficient approximation retains every spatial support and density bound. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMASpatialXZModel.withCoefficients {A B : ℕ} (M : QMASpatialXZModel A B)
    (K : M.Term → ℝ) : QMASpatialXZModel A B :=
  { M with coefficient := K }

theorem QMASpatialXZModel.round_energy {A B : ℕ} (M : QMASpatialXZModel A B)
    (N : ℕ) (hN : 0 < N) :
    let m := (Fintype.card M.Term+1)*N
    |(M.withCoefficients (fun e => (qmaRationalRound m (M.coefficient e):ℝ))).toQMAXZModel.energy-
      M.toQMAXZModel.energy| ≤ 1/(N:ℝ) := by
  have h := qmaPauliFamily_round_accuracy M.word M.coefficient N hN
  dsimp only at h ⊢
  rw [abs_sub_comm]
  exact h

end ContinuumCoulomb

end

end OAI
