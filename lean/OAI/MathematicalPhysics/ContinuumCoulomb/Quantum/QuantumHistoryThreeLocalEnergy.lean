import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryThreeLocal

namespace OAI

/-! Full-space energy comparison for the literal three-local history family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open scoped Classical

private theorem familyBottom_instances {ι κ : Type}
    (F G : Fintype ι) (d e : DecidableEq ι) (P Q : Fintype κ)
    (w : κ → ι → Fin 4) (J : κ → ℝ) :
    (letI := F; letI := d; letI := P;
      MediatorGraph.normalizedBottom (qmaPauliFamily w J)) =
    (letI := G; letI := e; letI := Q;
      MediatorGraph.normalizedBottom (qmaPauliFamily w J)) := by
  cases Subsingleton.elim F G
  cases Subsingleton.elim d e
  cases Subsingleton.elim P Q
  rfl

private theorem normalizedBottom_instances {α : Type}
    (F G : Fintype α) (d e : DecidableEq α) (H : Matrix α α ℂ) :
    @MediatorGraph.normalizedBottom α F d H =
      @MediatorGraph.normalizedBottom α G e H := by
  cases Subsingleton.elim F G
  cases Subsingleton.elim d e
  rfl

private theorem bottomError_instances {α : Type}
    (F G : Fintype α) (d e : DecidableEq α) (H : Matrix α α ℂ) (E r : ℝ)
    (h : |@MediatorGraph.normalizedBottom α F d H-E| ≤ r) :
    |@MediatorGraph.normalizedBottom α G e H-E| ≤ r := by
  rw [normalizedBottom_instances G F e d H]
  exact h

private theorem threeLocal_energy_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) : threeLocalEnergy c hT N =
    MediatorGraph.normalizedBottom (qmaPauliFamily
      (QuantumOrderedTwoStage.word (historySites c hT) (orderedWord c hT))
      (fun p => (QuantumOrderedTwoStage.coefficient
        (sampledOrderedWeight (samplePrecision c N) c hT) N p:ℝ))) := by
  unfold threeLocalEnergy threeLocalWord threeLocalCoefficient
  exact familyBottom_instances _ _ _ _ _ _ _ _

private theorem sampledHistory_energy_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) : sampledHistoryEnergy c hT N =
    MediatorGraph.normalizedBottom (qmaPauliFamily (orderedWord c hT)
      (fun p => (sampledOrderedWeight (samplePrecision c N) c hT p:ℝ))) := by
  unfold sampledHistoryEnergy
  exact familyBottom_instances _ _ _ _ _ _ _ _

private theorem history_twoStage_error (c : QMACircuit) (hT : 0 < c.gates.length)
    (J : OrderedPauliTerm c hT → ℚ) (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily
      (QuantumOrderedTwoStage.word (historySites c hT) (orderedWord c hT))
      (fun p => (QuantumOrderedTwoStage.coefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily (orderedWord c hT)
        (fun p => (J p:ℝ)))| ≤ 2/(N:ℝ) := by
  have h := QuantumOrderedTwoStage.accuracy
    (ι := (qmaOrderedHistoryModel c hT).Q) (κ := OrderedPauliTerm c hT)
    (historySites c hT) (orderedWord c hT)
    J (historySites_nodup c hT) (historySites_cover c hT) N hN
  exact bottomError_instances _ _ _ _ _ _ _ h

theorem threeLocal_sampled_error (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |threeLocalEnergy c hT N-sampledHistoryEnergy c hT N| ≤ 2/(N:ℝ) := by
  rw [threeLocal_energy_eq,sampledHistory_energy_eq]
  exact history_twoStage_error c hT
    (sampledOrderedWeight (samplePrecision c N) c hT) N (by omega)

theorem sampledHistory_error (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |sampledHistoryEnergy c hT N-(qmaOrderedHistoryModel c hT).energy| ≤ 1/(N:ℝ) :=
  sampledOrdered_accuracy c hT N hN

theorem threeLocal_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |threeLocalEnergy c hT N-(qmaOrderedHistoryModel c hT).energy| ≤ 3/(N:ℝ) := by
  exact (abs_sub_le (threeLocalEnergy c hT N) (sampledHistoryEnergy c hT N)
    (qmaOrderedHistoryModel c hT).energy).trans
      ((add_le_add (threeLocal_sampled_error c hT N hN)
        (sampledHistory_error c hT N hN)).trans_eq (by ring))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
