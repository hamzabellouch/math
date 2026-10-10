import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedOutputSpatial

namespace OAI

/-! The actual sparse verifier history has a fixed-density, degree-three
spatial exchange output. Its energy is that of the literal fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumPaddedLabelProgram
open QuantumForkList
open scoped Classical

def rawDensity : ℕ := 4*(45+3717*(4096*64))
def finalDensity : ℕ := spatialDensity rawDensity historyDegree

theorem padded_anchor_density (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    (Finset.univ.filter (fun a : Term (qmaSparseCircuit c) =>
      qmaOrderedTermCell c hT a.1=p)).card ≤ 4096*64 := by
  rw [qmaProductFilter_card (β := Fin 6 → Fin 4) (fun a => qmaOrderedTermCell c hT a=p)]
  simp only [Fintype.card_fun,Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (qmaOrderedTermCell_fiber_card c hT hne p)

def input (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    SpatialInput (qmaNearestCircuit c).gates.length c.work rawDensity historyDegree := by
  change SpatialInput _ _ (4*(45+3717*(4096*64))) (6+22*(12544*2359296))
  exact QuantumOrderedOutputSpatial.input (qubits (qmaSparseCircuit c))
    (sourceTerms (qmaSparseCircuit c) hT)
    (fun p : Term (qmaSparseCircuit c) => QuantumOrderedSupport.sites (qmaSparseCircuit c) hT p.1)
    (sourceWord (qmaSparseCircuit c) hT)
    (sampledWeight (QuantumAlgebraicHistory.samplePrecision (qmaSparseCircuit c) N)
      (qmaSparseCircuit c) hT)
    (fun p => QuantumOrderedSupport.sites_length (qmaSparseCircuit c) hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup (qmaSparseCircuit c) hT p.1)
    (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1)
    (by intro p; simpa only [Finset.filter_congr_decidable] using qmaOrderedQubitCell_fiber_card c hT hne p)
    (by intro p; simpa only [Finset.filter_congr_decidable] using padded_anchor_density c hT hne p)
    (fun p i hi => qmaOrderedHistoryModel_spatial c hc hT hne p.1 i
      ((QuantumOrderedSupport.sites_finset (qmaSparseCircuit c) hT p.1) ▸
        List.mem_toFinset.mpr hi))
    (by decide) (QuantumHistoryIncidence.sparse_padded_bound c hc hT hne) N

theorem input_state (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).state=forkState (qmaSparseCircuit c) hT N historyDegree := by
  unfold SpatialInput.state forkState historyQubits historyOutput historyInput
  rw [sourceEntries_table]
  rfl

def model (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) := (input c hc hT hne N).model

theorem model_energy (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).energy =
      MediatorGraph.normalizedBottom (matrix (forkState (qmaSparseCircuit c) hT N historyDegree)) := by
  rw [model,SpatialInput.model_energy,input_state]

theorem model_history_error (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) (hN : 0 < N) :
    |(model c hc hT hne N).energy-(qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy| ≤
      ((historyDegree:ℝ)+10)/(N:ℝ) := by
  rw [model_energy]
  exact fork_accuracy (qmaSparseCircuit c) hT N hN historyDegree

theorem model_degree (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ)
    (v : Fin (model c hc hT hne N).n) :
    qmaGraphDegree (model c hc hT hne N).left (model c hc hT hne N).right v ≤ 3 :=
  (input c hc hT hne N).model_degree v

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
