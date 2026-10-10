import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnarySoundness

namespace OAI

/-! Isometric embedding of the finite history into all unary clock strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnaryInclusion (c : QMACircuit) (p : QMAHistoryBasis c) : QMAUnaryBasis c :=
  (qmaHistoryClock c.gates.length p.1,p.2)

theorem qmaUnaryInclusion_injective (c : QMACircuit) : Function.Injective (qmaUnaryInclusion c) := by
  intro p q h
  change (qmaHistoryClock c.gates.length p.1,p.2) =
    (qmaHistoryClock c.gates.length q.1,q.2) at h
  apply Prod.ext
  · exact qmaHistoryClock_injective c.gates.length (congrArg Prod.fst h)
  · exact congrArg (fun r : QMAUnaryBasis c => r.2) h

def qmaUnaryExtend (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) : QMAUnaryBasis c → ℂ :=
  Function.extend (qmaUnaryInclusion c) u (fun _ => 0)

@[simp] theorem qmaUnaryExtend_valid (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : Fin (c.gates.length+1)) (a : SourceSpinBasis (c.work+1)) :
    qmaUnaryExtend c u (qmaHistoryClock c.gates.length t,a) = u (t,a) :=
  (qmaUnaryInclusion_injective c).extend_apply u (fun _ => 0) (t,a)

theorem qmaUnaryExtend_zero (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (s : SourceSpinBasis (c.gates.length+2)) (a : SourceSpinBasis (c.work+1))
    (hs : ¬QMALegalClock c.gates.length s) : qmaUnaryExtend c u (s,a) = 0 := by
  apply Function.extend_apply'
  rintro ⟨p,hp⟩
  apply hs
  have h := qmaHistoryClock_legal c.gates.length p.1
  rwa [show qmaHistoryClock c.gates.length p.1 = s from congrArg Prod.fst hp] at h

@[simp] theorem qmaUnaryRestrict_extend (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryRestrict c (qmaUnaryExtend c u) = u := by
  funext p
  exact qmaUnaryExtend_valid c u p.1 p.2

theorem qmaUnaryExtend_invalid_mass (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryInvalidMass c (qmaUnaryExtend c u) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : QMALegalClock c.gates.length s
  · simp only [ite_eq_left hs]
  · simp only [ite_eq_right hs,qmaUnaryExtend_zero c u s _ hs,Complex.normSq_zero,Finset.sum_const_zero]

theorem qmaUnaryExtend_mass (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryMass c (qmaUnaryExtend c u) = ∑ p, Complex.normSq (u p) := by
  rw [qmaUnaryMass_split,qmaUnaryRestrict_extend,qmaUnaryExtend_invalid_mass,add_zero]

theorem qmaUnaryExtend_clock_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryClockEnergy c (qmaUnaryExtend c u) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : QMALegalClock c.gates.length s
  · rw [qmaPinnedClockPenalty_zero _ _ hs,zero_mul]
  · simp only [qmaUnaryExtend_zero c u s _ hs,Complex.normSq_zero,Finset.sum_const_zero,mul_zero]

theorem qmaUnaryResidual_extend_invalid (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : Fin c.gates.length) (s : SourceSpinBasis (c.gates.length+2))
    (hg : QMAClockGuard c.gates.length t s) (hz : s (qmaClockMiddle c.gates.length t) = 0)
    (hs : ¬QMALegalClock c.gates.length s) (a : SourceSpinBasis (c.work+1)) :
    qmaUnaryResidual c (qmaUnaryExtend c u) t s a = 0 := by
  have ha : ¬QMALegalClock c.gates.length (Function.update s (qmaClockMiddle c.gates.length t) 1) :=
    fun h => hs ((qmaClock_step_legal_iff c.gates.length t s hg hz).mp h)
  have he : (fun b => qmaUnaryExtend c u (s,b)) = 0 := by
    funext b
    exact qmaUnaryExtend_zero c u s b hs
  unfold qmaUnaryResidual
  rw [he,Matrix.mulVec_zero,qmaUnaryExtend_zero c u _ a ha]
  simp

end ContinuumCoulomb

end

end OAI
