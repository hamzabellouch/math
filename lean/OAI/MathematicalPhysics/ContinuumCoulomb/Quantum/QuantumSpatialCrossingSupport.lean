import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCrossingGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumScheduleCrossingGeometry

namespace OAI

/-! The actual spatial compiler emits a crossing packet with the canonical
physical support and positions, rather than merely an abstract simulation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N : ℚ)

theorem packet_geometry :
    QMAPacketGeometry
      ((I.model.portRouteData hA I.model_degree).crossingOutput N (length_bound I hA))
      ((I.model.portRouteData hA I.model_degree).crossingPosition N
        (QuantumSpatialPortProgram.rounds A D))
      (value A D (N,QuantumSpatialInputTape.input I)).1.1
      (value A D (N,QuantumSpatialInputTape.input I)).1.2 := by
  let P := I.model.portRouteData hA I.model_degree
  let S := (QuantumSpatialPortProgram.value A D (N,QuantumSpatialInputTape.input I)).1
  obtain ⟨hs,Ps,E,hrep,hpos,hpoint⟩ := QuantumSpatialPortProgram.value_matches I hA N
  obtain ⟨cell,hcell⟩ := cells_order I hA N
  have hp : oldPositions A D (N,QuantumSpatialInputTape.input I) =
      List.ofFn (fun v => P.finishedPosition N (QuantumSpatialPortProgram.rounds A D)
        (E.vertex v)) := by
    apply hrep.1.trans
    exact congrArg List.ofFn (funext fun v => (hpos v).symm)
  have hsites : sites A D (N,QuantumSpatialInputTape.input I) =
      List.ofFn (QuantumCrossingSelectProgram.encodedSites
        (QuantumScheduleCrossingGeometry.site P N (length_bound I hA) S hs E cell)) := by
    change QuantumCrossingSiteProgram.allSites
      (oldPositions A D (N,QuantumSpatialInputTape.input I),
        cells A D (N,QuantumSpatialInputTape.input I)) = _
    apply (congrArg QuantumCrossingSiteProgram.allSites (congrArg₂ Prod.mk hp hcell)).trans
    exact QuantumCrossingSiteProgram.allSites_reordered P N (length_bound I hA) E.vertex
      (fun v => P.finishedPosition N (QuantumSpatialPortProgram.rounds A D) (E.vertex v))
      (fun _ => rfl) cell
  have hinput : crossingInput A D (N,QuantumSpatialInputTape.input I) =
      QuantumScheduleCrossingGeometry.input P N (length_bound I hA) S hs E cell := by
    exact congrArg (fun ss => QuantumCrossingSelectProgram.value
      (N,oldPacket A D (N,QuantumSpatialInputTape.input I),ss)) hsites
  have hpositions : positions A D (N,QuantumSpatialInputTape.input I) =
      QuantumCrossingPositionProgram.positions
        (List.ofFn (fun i => (P.crossingCell (cell i)).val),
          List.ofFn (fun v => P.finishedPosition N (QuantumSpatialPortProgram.rounds A D)
            (E.vertex v))) :=
    congrArg QuantumCrossingPositionProgram.positions (congrArg₂ Prod.mk hcell hp)
  change QMAPacketGeometry (P.crossingOutput N (length_bound I hA))
    (P.crossingPosition N (QuantumSpatialPortProgram.rounds A D))
    (QuantumCrossingListLayer.value (crossingInput A D (N,QuantumSpatialInputTape.input I)))
    (positions A D (N,QuantumSpatialInputTape.input I))
  rw [hinput,hpositions]
  exact QuantumScheduleCrossingGeometry.packet_geometry P N (length_bound I hA) S hs E cell

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
