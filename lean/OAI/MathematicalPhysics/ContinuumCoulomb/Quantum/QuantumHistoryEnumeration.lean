import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedPositive
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceComparison

namespace OAI

/-! Explicit consecutive labels for every term in the distributed history. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := by fin_cases i; rfl

abbrev qmaHistoryReferenceWork (c : QMACircuit) : ℕ := 2*c.gates.length+c.work+4

def qmaHistoryTermIndex (c : QMACircuit) : QMACircuitTerm c ≃ Fin (qmaHistoryReferenceWork c+1) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _)
      ((Equiv.sumCongr (Equiv.refl _)
        ((Equiv.sumCongr qmaUnitFin (Equiv.refl _)).trans finSumFinEquiv)).trans
          finSumFinEquiv)).trans finSumFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr (by unfold qmaHistoryReferenceWork; omega)))

def qmaHistoryReferenceTerms (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) :=
  qmaDistributedTermMatrix c τ ((qmaHistoryTermIndex c).symm i)

theorem qmaHistoryReferenceTerms_sum (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (∑ i, qmaHistoryReferenceTerms c τ i) = qmaDistributedQubitHamiltonian c τ := by
  unfold qmaHistoryReferenceTerms
  rw [(qmaHistoryTermIndex c).symm.sum_comp,qmaDistributedTerm_sum]

theorem qmaHistoryReferenceTerms_nonnegative (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1))
    (u : (QMACircuitQubit c → Fin 2) → ℂ) :
    0 ≤ qmaQuadratic (qmaHistoryReferenceTerms c τ i) u :=
  qmaDistributedTerm_nonnegative c τ _ u

end ContinuumCoulomb

end

end OAI
