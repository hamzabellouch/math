import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCrossingSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFinalRoutingProgram

namespace OAI

/-! Full-space error of the complete literal routing program. The sum pays
for the actual port, crossing, parity and final subdivision stages. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open QuantumForkList

theorem planar_energy (x : QuantumPlanarTapeProgram.Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1) :
    QuantumCrossingPacketEnergy.energy (QuantumPlanarTapeProgram.value x).1 =
      QuantumCrossingPacketEnergy.energy x.1.1 := by
  change sourceMatrixBottom x.1.1.1
    (SourceBondLists.matrix x.1.1.1 (QuantumListMerge.value x.1.1.1 x.1.1.2.1)+
      (x.1.1.2.2:ℂ) • 1) = _
  rw [QuantumListMerge.matrix_eq _ _ hb]
  rfl

theorem spatial_planar_noLoops {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N a b : ℚ) :
    ∀ e ∈ (planar A D ((N,QuantumSpatialInputTape.input I),a,b)).1.2.1,
      e.1 ≠ e.2.1 := by
  have h := QuantumListMerge.noLoops
    (n := (QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I)).1.1.1)
    (xs := (QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I)).1.1.2.1)
    (QuantumSpatialCrossingProgram.packet_geometry I hA N).noLoops
  simpa only [planar,QuantumPlanarTapeProgram.value,QuantumPlanarTapeProgram.merged] using h

theorem spatial_planar_energy {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N a b : ℚ) :
    QuantumCrossingPacketEnergy.energy (planar A D ((N,QuantumSpatialInputTape.input I),a,b)).1 =
      QuantumCrossingPacketEnergy.energy
        (QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I)).1.1 := by
  exact planar_energy _ (QuantumSpatialCrossingProgram.packet_geometry I hA N).bounded

theorem spatial_routed_energy_error {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 < N) (a b : ℚ) :
    |QuantumListSchedule.energy (routed A D ((N,QuantumSpatialInputTape.input I),a,b)).1-
      QuantumCrossingPacketEnergy.energy
        (QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I)).1.1| ≤
      81/(N:ℝ) := by
  have h := energy_error A D ((N,QuantumSpatialInputTape.input I),a,b) hN
    (spatial_planar_noLoops I hA N a b)
  rw [← spatial_planar_energy I hA N a b]
  exact h

private theorem sum_error {a b c d n r : ℝ}
    (hab : |a-b| ≤ 81/n) (hbc : |b-c| ≤ 1/n) (hcd : |c-d| ≤ r/n) :
    |a-d| ≤ (r+82)/n := by
  calc
    _ ≤ |a-b|+|b-c|+|c-d| :=
      le_trans (abs_sub_le a c d) (by linarith [abs_sub_le a b c])
    _ ≤ 81/n+1/n+r/n := add_le_add (add_le_add hab hbc) hcd
    _ = _ := by ring

theorem spatial_energy_error {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 < N) (a b : ℚ) :
    |QuantumListSchedule.energy (routed A D ((N,QuantumSpatialInputTape.input I),a,b)).1-
      I.model.energy| ≤ ((QuantumSpatialPortProgram.rounds A D:ℝ)+82)/(N:ℝ) := by
  have hf := spatial_routed_energy_error I hA hN a b
  have hc := QuantumSpatialCrossingProgram.energy_error I hA hN
  obtain ⟨_,_,_,_,_,_,hp⟩ := QuantumSpatialPortProgram.realizes I hA hN
  exact sum_error hf hc hp

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
