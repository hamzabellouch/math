import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialFinalGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialFinalEnergy

namespace OAI

/-! Routing retains every original spin. This supplies positivity of the
emitted lattice size and its comparison with the history input size. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open QuantumForkList

theorem crossing_count_le (A D : ℕ) (x : QuantumSpatialPortProgram.Input) :
    (QuantumSpatialPortProgram.value A D x).1.1 ≤
      (QuantumSpatialCrossingProgram.value A D x).1.1.1 := by
  change (QuantumSpatialPortProgram.value A D x).1.1 ≤
    (QuantumSpatialPortProgram.value A D x).1.1+_
  exact Nat.le_add_right _ _

theorem even_count_le (A D : ℕ) (x : Input) :
    (QuantumSpatialCrossingProgram.value A D x.1).1.1.1 ≤ (even A D x).1.1 := by
  change (QuantumSpatialCrossingProgram.value A D x.1).1.1.1 ≤
    (QuantumSpatialCrossingProgram.value A D x.1).1.1.1+_
  exact Nat.le_add_right _ _

theorem initial_count_le (A D : ℕ) (x : Input) :
    (QuantumSpatialPortProgram.initial A D x.1.2).1.1 ≤ (routed A D x).1.1 := by
  have hp := QuantumListRouteProgram.iterate_count_le x.1.1
    (QuantumSpatialPortProgram.initial A D x.1.2) (QuantumSpatialPortProgram.rounds A D)
  have hf := QuantumListRouteProgram.iterate_count_le x.1.1 (even A D x) rounds
  exact hp.trans ((crossing_count_le A D x.1).trans ((even_count_le A D x).trans hf))

theorem spatial_count_le {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N a b : ℚ) :
    I.model.n ≤ (routed A D ((N,QuantumSpatialInputTape.input I),a,b)).1.1 := by
  have h := initial_count_le A D ((N,QuantumSpatialInputTape.input I),a,b)
  have hi := congrArg (fun s : QuantumListSchedule.State => s.1)
    (QuantumPortSchedulePacking.state_eq I hA)
  have hh : (QuantumSpatialPortProgram.initial A D (QuantumSpatialInputTape.input I)).1.1 =
      I.model.n := hi
  exact hh ▸ h

theorem spatial_crossing_count_le {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N : ℚ) :
    I.model.n ≤ (QuantumSpatialCrossingProgram.value A D
      (N,QuantumSpatialInputTape.input I)).1.1.1 := by
  have hp := QuantumListRouteProgram.iterate_count_le N
    (QuantumSpatialPortProgram.initial A D (QuantumSpatialInputTape.input I))
    (QuantumSpatialPortProgram.rounds A D)
  have hi := congrArg (fun s : QuantumListSchedule.State => s.1)
    (QuantumPortSchedulePacking.state_eq I hA)
  have hh : (QuantumSpatialPortProgram.initial A D (QuantumSpatialInputTape.input I)).1.1 =
      I.model.n := hi
  exact hh ▸ hp.trans (crossing_count_le A D (N,QuantumSpatialInputTape.input I))

theorem spatial_valid {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 < N)
    (hn : 0 < I.model.n) (a b : ℚ) (hab : a < b) :
    (value A D ((N,QuantumSpatialInputTape.input I),a,b)).Valid := by
  obtain ⟨hs,Q,hQ,_,hgrid⟩ := spatial_realization I hA hN a b
  exact QuantumListRouteProgram.latticeOutput_valid _ hs Q hQ hgrid
    (hn.trans_le (spatial_count_le I hA N a b)) a b hab

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
