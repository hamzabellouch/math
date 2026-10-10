import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockSector
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCountedHistory

namespace OAI

/-! The full unary-clock form retains every clock configuration. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMAUnaryBasis (c : QMACircuit) :=
  SourceSpinBasis (c.gates.length+2) × SourceSpinBasis (c.work+1)

def qmaUnaryRestrict (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : QMAHistoryBasis c → ℂ :=
  fun p => u (qmaHistoryClock c.gates.length p.1,p.2)

def qmaUnaryMass (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ p, Complex.normSq (u p)

def qmaUnaryInvalidMass (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2),
    if QMALegalClock c.gates.length s then 0 else ∑ a, Complex.normSq (u (s,a))

def qmaUnaryClockEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2),
    qmaPinnedClockPenalty c.gates.length s * ∑ a, Complex.normSq (u (s,a))

theorem qmaUnaryMass_split (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaUnaryMass c u =
      (∑ p : QMAHistoryBasis c, Complex.normSq (qmaUnaryRestrict c u p))+
      qmaUnaryInvalidMass c u := by
  unfold qmaUnaryMass qmaUnaryInvalidMass qmaUnaryRestrict
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  exact qmaClock_sector_sum c.gates.length (fun s => ∑ a, Complex.normSq (u (s,a)))

theorem qmaUnaryInvalidMass_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaUnaryInvalidMass c u ≤ qmaUnaryClockEnergy c u := by
  apply qmaClock_invalid_mass_bound
  intro s
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg (u (s,a)))

def qmaUnaryResidual (c : QMACircuit) (u : QMAUnaryBasis c → ℂ)
    (t : Fin c.gates.length) (s : SourceSpinBasis (c.gates.length+2)) :
    SourceSpinBasis (c.work+1) → ℂ :=
  fun a => u (Function.update s (qmaClockMiddle c.gates.length t) 1,a)-
    (qmaStepMatrix c t.val).mulVec (fun b => u (s,b)) a

def qmaUnaryPropagationEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ t : Fin c.gates.length, ∑ s : SourceSpinBasis (c.gates.length+2),
    if QMAClockGuard c.gates.length t s ∧ s (qmaClockMiddle c.gates.length t) = 0 then
      ∑ a, Complex.normSq (qmaUnaryResidual c u t s a) else 0

theorem qmaUnaryResidual_valid (c : QMACircuit) (u : QMAUnaryBasis c → ℂ)
    (t : Fin c.gates.length) (a : SourceSpinBasis (c.work+1)) :
    qmaUnaryResidual c u t (qmaHistoryClock c.gates.length t.castSucc) a =
      (qmaPropagationMatrix c).mulVec (qmaUnaryRestrict c u) (t,a) := by
  rw [qmaPropagationMatrix,LinearMap.toMatrix'_mulVec]
  unfold qmaUnaryResidual
  rw [qmaClock_step_update]
  rfl

theorem qmaUnaryPropagationEnergy_valid_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaPropagationEnergy c (qmaHistoryFromVector c (qmaUnaryRestrict c u)) ≤
      qmaUnaryPropagationEnergy c u := by
  rw [←qmaPropagationMatrix_energy,qmaQuadratic_gram,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro t _
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if QMAClockGuard c.gates.length t s ∧ s (qmaClockMiddle c.gates.length t) = 0 then
        ∑ a, Complex.normSq (qmaUnaryResidual c u t s a) else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length t.castSucc)
    (by intro s _; split
        · exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
        · exact le_rfl) (Finset.mem_univ _)
  have hg : QMAClockGuard c.gates.length t (qmaHistoryClock c.gates.length t.castSucc) ∧
      qmaHistoryClock c.gates.length t.castSucc (qmaClockMiddle c.gates.length t) = 0 :=
    ⟨qmaClock_step_guard c.gates.length t,qmaClock_step_zero c.gates.length t⟩
  simpa only [ite_eq_left hg,qmaUnaryResidual_valid] using h

end ContinuumCoulomb

end

end OAI
