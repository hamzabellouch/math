import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPortMatching
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCrossingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialRoutingTape
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSiteRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPositionRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPacketEnergy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutePermissionCongr

namespace OAI

/-! The computed crossing cells and terminal scans use exactly the physical
port geometry, with finite permutations accounting for their output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList QuantumRouteCode
open scoped Classical

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N : ℚ)

private def edgeList := List.ofFn (fun e : I.model.Term => e)

private theorem edgeList_complete (e : I.model.Term) : e ∈ edgeList I :=
  List.mem_ofFn.mpr ⟨e,rfl⟩

private theorem ofFn_map_id {n : ℕ} {α : Type*} (f : Fin n → α) :
    List.ofFn f = (List.ofFn (fun e : Fin n => e)).map f := by
  rw [List.map_ofFn]
  rfl

theorem coarse_actual : coarse A D (N,QuantumSpatialInputTape.input I) =
    (List.ofFn (I.model.portRouteData hA I.model_degree).position,
      (edgeList I).map (I.model.portRouteData hA I.model_degree).routeList) := by
  have h := QuantumSpatialRoutingTape.value_actual I hA
  change QuantumSpatialRoutingTape.value A D (QuantumSpatialInputTape.input I) = _
  rw [h]
  refine Prod.ext ?_ ?_
  · rfl
  exact ofFn_map_id (fun e : Fin (fullList I.state).length =>
    (I.model.portRouteData hA I.model_degree).routeList e)

theorem cells_order :
    ∃ τ : Fin (cells A D (N,QuantumSpatialInputTape.input I)).length ≃
      Fin (I.model.portRouteData hA I.model_degree).crossingCells.card,
      cells A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (fun i => ((I.model.portRouteData hA I.model_degree).crossingCell (τ i)).val) := by
  unfold cells
  rw [coarse_actual I hA N]
  let P := I.model.portRouteData hA I.model_degree
  refine ⟨(QuantumDistinctCrossings.cellsEquiv P (edgeList I) (edgeList_complete I)).trans
    P.crossingCells.equivFin,?_⟩
  apply (QuantumDistinctCrossings.list_eq P (edgeList I) (edgeList_complete I)).trans
  apply congrArg List.ofFn
  funext i
  change ((QuantumDistinctCrossings.cellsEquiv P (edgeList I) (edgeList_complete I)) i).val =
    (P.crossingCells.equivFin.symm (P.crossingCells.equivFin
      ((QuantumDistinctCrossings.cellsEquiv P (edgeList I) (edgeList_complete I)) i))).val
  rw [Equiv.symm_apply_apply]

theorem old_positions_order :
    ∃ σ : Fin (oldPacket A D (N,QuantumSpatialInputTape.input I)).1 ≃
      Fin ((I.model.portRouteData hA I.model_degree).finishedGraph N
        (QuantumSpatialPortProgram.rounds A D)).n,
      oldPositions A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (fun v => (I.model.portRouteData hA I.model_degree).finishedPosition N
          (QuantumSpatialPortProgram.rounds A D) (σ v)) := by
  obtain ⟨hk,Pk,Ek,hrep,hpos,_⟩ := QuantumSpatialPortProgram.value_matches I hA N
  refine ⟨Ek.vertex,hrep.1.trans ?_⟩
  apply congrArg List.ofFn
  funext v
  exact (hpos v).symm

theorem table_permission (R : QMACellRouteBody) :
    QuantumRoutingTable.allowed (table A D (N,QuantumSpatialInputTape.input I)) R =
      QuantumRoutingTable.allowed (I.model.portRouteData hA I.model_degree).routingTable R := by
  unfold table
  rw [coarse_actual I hA N]
  exact QuantumPathTable.compile_allowed _ _ (edgeList_complete I) R

theorem length_bound (e : I.model.Term) :
    (I.model.portRouteData hA I.model_degree).length e ≤
      QuantumSpatialPortProgram.rounds A D := by
  rw [← QuantumSpatialPortProgram.rounds_eq]
  exact I.model.bufferedPath_length I.model_degree e

theorem sites_positions_order :
    ∃ (σ : Fin (oldPacket A D (N,QuantumSpatialInputTape.input I)).1 ≃
      Fin ((I.model.portRouteData hA I.model_degree).finishedGraph N
        (QuantumSpatialPortProgram.rounds A D)).n)
      (τ : Fin (cells A D (N,QuantumSpatialInputTape.input I)).length ≃
        Fin (I.model.portRouteData hA I.model_degree).crossingCells.card),
      sites A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (QuantumCrossingSelectProgram.encodedSites
          (fun i a => σ.symm ((I.model.portRouteData hA I.model_degree).crossingSiteFin N
            (length_bound I hA) (τ i) a))) ∧
      positions A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (fun v => (I.model.portRouteData hA I.model_degree).crossingPosition N
          (QuantumSpatialPortProgram.rounds A D)
          (QuantumCrossingPositionProgram.extend _ _ _ σ τ v)) := by
  obtain ⟨σ,hσ⟩ := old_positions_order I hA N
  obtain ⟨τ,hτ⟩ := cells_order I hA N
  refine ⟨σ,τ,?_,?_⟩
  · unfold sites
    apply (congrArg QuantumCrossingSiteProgram.allSites
      (congrArg₂ Prod.mk hσ hτ)).trans
    exact QuantumCrossingSiteProgram.allSites_reordered _ N (length_bound I hA) σ
      (fun v => (I.model.portRouteData hA I.model_degree).finishedPosition N
        (QuantumSpatialPortProgram.rounds A D) (σ v)) (fun _ => rfl) τ
  · unfold positions
    apply (congrArg QuantumCrossingPositionProgram.positions
      (congrArg₂ Prod.mk hτ hσ)).trans
    exact QuantumCrossingPositionProgram.positions_reordered _ _ _ σ τ

include hA in
theorem energy_error {N : ℚ} (hN : 0 < N) :
    |QuantumCrossingPacketEnergy.energy (value A D (N,QuantumSpatialInputTape.input I)).1.1 -
      QuantumCrossingPacketEnergy.energy (oldPacket A D (N,QuantumSpatialInputTape.input I))| ≤
        1/(N:ℝ) := by
  obtain ⟨hk,Pk,Ek,hrep,hpos,hpoint⟩ := QuantumSpatialPortProgram.value_matches I hA N
  obtain ⟨σ,τ,hsite,_⟩ := sites_positions_order I hA N
  change |QuantumCrossingPacketEnergy.energy (QuantumCrossingListLayer.value
    (QuantumCrossingSelectProgram.value (N,oldPacket A D (N,QuantumSpatialInputTape.input I),
      sites A D (N,QuantumSpatialInputTape.input I)))) - _| ≤ _
  rw [hsite]
  exact QuantumCrossingPacketEnergy.list_error _ _ _ hk.1 hk.2 _
    (QuantumCrossingSiteProgram.reordered_sites_global _ N (length_bound I hA) σ τ) hN

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
