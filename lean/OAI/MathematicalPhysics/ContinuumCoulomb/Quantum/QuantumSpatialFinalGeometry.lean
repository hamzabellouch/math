import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPacketRoutingGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCrossingSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPlanarRealization

namespace OAI

/-! The complete literal spatial routing output carries the exact physical
square-lattice embedding, with a fixed multiple of the original box. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open QuantumForkList

theorem spatial_realization {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 < N) (a b : ℚ) :
    let s := routed A D ((N,QuantumSpatialInputTape.input I),a,b)
    ∃ (hs : QuantumListSchedule.Valid s.1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule s.1 hs)),
      QuantumListRouteProgram.Represents s hs Q ∧
      Q.Bounded (256*I.model.bufferedWidth) (256*I.model.bufferedHeight) ∧
      (∀ e, qmaSquareGrid.Adj (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.left e))
        (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.right e))) := by
  let P := I.model.portRouteData hA I.model_degree
  have hpath : ∀ e k, k ≤ P.length e →
      (P.point e k).1 < I.model.bufferedWidth ∧
      (P.point e k).2 < I.model.bufferedHeight := by
    intro e k _
    exact I.model.bufferedPath_bounds I.model_degree e
      ((I.model.bufferedPath I.model_degree e).val.getVert_mem_support k)
  exact QuantumPlanarTapeGeometry.final_realization P N
    (QuantumSpatialCrossingProgram.length_bound I hA)
    (QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I))
    (QuantumSpatialCrossingProgram.packet_geometry I hA N)
    (QuantumSpatialCrossingProgram.table_permission I hA N)
    (I.model.sourceCell_no_passage hA I.model_degree) I.model.placedVertex_positive
    I.model.placedVertex_bounds hpath hN

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
