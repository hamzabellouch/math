import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySampling
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedTwoStage

namespace OAI

/-! The actual circuit-history Hamiltonian is sent to an explicitly
specified rational three-local even-Y family.  Sampling and the two
subdivision stages each have their own inverse-precision error bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open scoped Classical

def historySites (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : List ((qmaOrderedHistoryModel c hT).Q) :=
  QuantumOrderedSupport.sites c hT p.val.1

theorem historySites_nodup (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : (historySites c hT p).Nodup :=
  QuantumOrderedSupport.sites_nodup c hT p.val.1

theorem historySites_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) : (historySites c hT p).length ≤ 6 :=
  QuantumOrderedSupport.sites_length c hT p.val.1

theorem historySites_cover (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) :
    qmaPauliSupport (orderedWord c hT p) ⊆ (historySites c hT p).toFinset := by
  have hsites : (historySites c hT p).toFinset =
      (qmaOrderedHistoryModel c hT).sites p.val.1 :=
    QuantumOrderedSupport.sites_finset c hT p.val.1
  have hsub : (qmaOrderedHistoryModel c hT).sites p.val.1 ⊆
      (historySites c hT p).toFinset := le_of_eq hsites.symm
  exact (qmaPauliExtend_support _ _).trans hsub

abbrev ThreeLocalTerm (c : QMACircuit) (hT : 0 < c.gates.length) :=
  (OrderedPauliTerm c hT × Fin 4) × Fin 4

abbrev ThreeLocalQubit (c : QMACircuit) (hT : 0 < c.gates.length) :=
  ((qmaOrderedHistoryModel c hT).Q ⊕ OrderedPauliTerm c hT) ⊕ (OrderedPauliTerm c hT × Fin 4)

def threeLocalWord (c : QMACircuit) (hT : 0 < c.gates.length) :
    ThreeLocalTerm c hT → ThreeLocalQubit c hT → Fin 4 :=
  QuantumOrderedTwoStage.word (ι := (qmaOrderedHistoryModel c hT).Q)
    (κ := OrderedPauliTerm c hT) (historySites c hT) (orderedWord c hT)

def threeLocalSites (c : QMACircuit) (hT : 0 < c.gates.length) :
    ThreeLocalTerm c hT → List (ThreeLocalQubit c hT) :=
  QuantumOrderedTwoStage.sites (historySites c hT)

def threeLocalCoefficient (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    ThreeLocalTerm c hT → ℚ :=
  QuantumOrderedTwoStage.coefficient
    (sampledOrderedWeight (samplePrecision c N) c hT) N

def threeLocalEnergy (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (threeLocalWord c hT)
    (fun p => (threeLocalCoefficient c hT N p:ℝ)))

def sampledHistoryEnergy (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (orderedWord c hT)
    (fun p => (sampledOrderedWeight (samplePrecision c N) c hT p:ℝ)))

theorem threeLocal_support (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : (OrderedPauliTerm c hT × Fin 4) × Fin 4) :
    (qmaPauliSupport (threeLocalWord c hT p)).card ≤ 3 :=
  QuantumOrderedTwoStage.support _ (historySites_length c hT) _ p

theorem threeLocal_even (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : (OrderedPauliTerm c hT × Fin 4) × Fin 4) :
    Even (qmaPauliYCount (threeLocalWord c hT p)) :=
  QuantumOrderedTwoStage.even _ _ (historySites_nodup c hT)
    (historySites_cover c hT) (orderedWord_even c hT) p

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
