import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySourceProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialFinalEnergy

namespace OAI

/-! Full-space history comparison and verifier implications for the
literal circuit-to-lattice output, including empty-circuit preparation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory

def routedState (c : QMACircuit) : QuantumListRouteProgram.State :=
  QuantumFinalRoutingProgram.routed rawDensity historyDegree (finalInput c)

theorem routedState_actual (c : QMACircuit) (hc : c.WellFormed) :
    routedState c = QuantumFinalRoutingProgram.routed rawDensity historyDegree
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        thresholds c) :=
  congrArg (QuantumFinalRoutingProgram.routed rawDensity historyDegree) (finalInput_actual c hc)

theorem route_rounds_eq : QuantumSpatialPortProgram.rounds rawDensity historyDegree = routeRounds :=
  (QuantumSpatialPortProgram.rounds_eq rawDensity historyDegree).symm.trans routeRounds_eq

theorem history_error (c : QMACircuit) (hc : c.WellFormed) :
    |QuantumListSchedule.energy (routedState c).1-
      (qmaOrderedHistoryModel (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)).energy| ≤
      ((totalRounds:ℝ)+9)/(precision c:ℝ) := by
  let d := qmaNonemptyCircuit c
  let hd := qmaNonemptyCircuit_wellFormed c hc
  let ht := qmaNonemptyCircuit_sparse_pos c
  let he := qmaNonemptyCircuit_nearest c
  have hr := QuantumFinalRoutingProgram.spatial_energy_error
    (QuantumHistorySpatial.input d hd ht he (precision c)) finalDensity_pos
    (N := (precision c:ℚ)) (by exact_mod_cast precision_pos c)
    (thresholds c).1 (thresholds c).2
  have hh := model_history_error d hd ht he (precision c) (precision_pos c)
  rw [route_rounds_eq] at hr
  rw [routedState_actual c hc]
  have hn : ((precision c:ℚ):ℝ) = (precision c:ℝ) := Rat.cast_natCast _
  rw [hn] at hr
  calc
    _ ≤ |QuantumListSchedule.energy
          (QuantumFinalRoutingProgram.routed rawDensity historyDegree
            (((precision c:ℚ),QuantumSpatialInputTape.input
              (QuantumHistorySpatial.input d hd ht he (precision c))),thresholds c)).1-
            (model d hd ht he (precision c)).energy|+
        |(model d hd ht he (precision c)).energy-
          (qmaOrderedHistoryModel (qmaPreparedCircuit c) ht).energy| := abs_sub_le _ _ _
    _ ≤ ((routeRounds:ℝ)+82)/(precision c:ℝ)+((historyDegree:ℝ)+10)/(precision c:ℝ) :=
      add_le_add hr hh
    _ = _ := by simp only [totalRounds,Nat.cast_add,Nat.cast_ofNat]; ring

theorem routed_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖=1)
    (ha : 2/3 ≤ qmaAcceptance c hc psi) :
    QuantumListSchedule.energy (routedState c).1 ≤ ((thresholds c).1:ℝ) := by
  exact final_accepting totalRounds (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)
    (qmaPreparedCircuit_wellFormed c hc) (history_error c hc) psi hpsi
    ((qmaPreparedCircuit_acceptance c hc psi).symm ▸ ha)

theorem routed_rejecting (c : QMACircuit) (hc : c.WellFormed)
    (ha : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖=1 → qmaAcceptance c hc psi ≤ 1/3) :
    ((thresholds c).2:ℝ) ≤ QuantumListSchedule.energy (routedState c).1 := by
  apply final_rejecting totalRounds (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)
    (qmaPreparedCircuit_wellFormed c hc) (history_error c hc)
  intro psi hpsi
  exact (qmaPreparedCircuit_acceptance c hc psi).symm ▸ ha psi hpsi

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
