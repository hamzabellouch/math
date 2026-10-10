import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCoefficient
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliRounding

namespace OAI

/-! Sampling the exact ordered-history coefficients controls the actual
full-space ground energy.  Odd-Y words are omitted by the proved real
Pauli expansion, leaving at most 4096 words per six-site history term. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

abbrev OrderedPauliTerm (c : QMACircuit) (hT : 0 < c.gates.length) :=
  QMALocalEvenPauliTerm (qmaOrderedHistoryModel c hT).sites

def orderedWord (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) :=
  qmaLocalPauliWord (qmaOrderedHistoryModel c hT).sites p.val

def orderedRealCoefficient (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : RealScalar :=
  realCoefficient (orderedCore c hT p.val.1) p.val.2

theorem orderedRealCoefficient_value (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) :
    realValue (orderedRealCoefficient c hT p) =
      qmaLocalPauliCoefficient (qmaOrderedHistoryModel c hT).matrix
        (qmaOrderedHistoryModel c hT).sites p.val :=
  orderedCoefficient_eq c hT p.val.1 p.val.2

theorem orderedWord_even (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : Even (qmaPauliYCount (orderedWord c hT p)) :=
  qmaLocalEvenPauli_even _ p

theorem orderedWord_support (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : (qmaPauliSupport (orderedWord c hT p)).card ≤ 6 :=
  qmaLocalEvenPauli_support _ (qmaOrderedHistoryModel c hT).card p

theorem orderedWord_count (c : QMACircuit) (hT : 0 < c.gates.length) :
    Fintype.card (OrderedPauliTerm c hT) ≤
      4096*(4*c.gates.length+2*c.work+9) := by
  have h := qmaLocalEvenPauli_count (qmaOrderedHistoryModel c hT).sites
    (qmaOrderedHistoryModel c hT).card
  have he := (qmaOrderedHistoryModel_size c hT).2
  change Fintype.card (OrderedPauliTerm c hT) ≤ 4^6*(qmaOrderedHistoryModel c hT).terms at h
  rw [he] at h
  norm_num only [show (4:ℕ)^6 = 4096 by norm_num] at h
  exact h

theorem orderedPauli_sum (c : QMACircuit) (hT : 0 < c.gates.length) :
    qmaPauliFamily (orderedWord c hT)
      (fun p => realValue (orderedRealCoefficient c hT p)) =
      ∑ a, (qmaOrderedHistoryModel c hT).matrix a := by
  simp only [qmaPauliFamily,orderedWord,orderedRealCoefficient_value]
  exact qmaLocalEvenPauli_sum _ _ (qmaOrderedHistoryModel c hT).localOn
    (qmaOrderedHistoryModel c hT).hermitian (qmaOrderedHistoryModel c hT).real

def sampledOrderedWeight (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : ℚ :=
  sample k (orderedRealCoefficient c hT p)

theorem sampledOrdered_error (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    |MediatorGraph.normalizedBottom
      (qmaPauliFamily (orderedWord c hT) (fun p => (sampledOrderedWeight k c hT p:ℝ))) -
        (qmaOrderedHistoryModel c hT).energy| ≤
      ∑ p : OrderedPauliTerm c hT,
        |((orderedRealCoefficient c hT p).2:ℝ)| * (2:ℝ)⁻¹^k := by
  change |MediatorGraph.normalizedBottom _ -
    MediatorGraph.normalizedBottom (∑ a, (qmaOrderedHistoryModel c hT).matrix a)| ≤ _
  rw [← orderedPauli_sum]
  apply (qmaPauliFamily_ground_error _ _ _).trans
  apply Finset.sum_le_sum
  intro p _
  exact QuantumAlgebraicScalar.sample_error k (orderedRealCoefficient c hT p)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
