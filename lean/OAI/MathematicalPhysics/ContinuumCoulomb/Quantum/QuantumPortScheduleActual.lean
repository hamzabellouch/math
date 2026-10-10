import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortScheduleTape

namespace OAI

/-! The computed schedule has precisely the coefficients, work counts and
physical port paths of the proved spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleActual
open QuantumForkList QuantumRouteCode QuantumPortScheduleTape

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)

abbrev tape := QuantumForkGridProgram.output D (QuantumSpatialInputTape.input I)

theorem bonds_ofFn : fullList I.state = List.ofFn (fun e : I.model.Term =>
    ((I.model.left e).val,(I.model.right e).val,I.model.weight e)) := by
  change fullList I.state = List.ofFn (fun i => (fullList I.state).get i)
  exact (List.ofFn_get (fullList I.state)).symm

include hA in
theorem entries_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1.2.2 =
      List.ofFn (fun e : I.model.Term =>
        (I.model.coarseLength I.model_degree e,
          (I.model.left e).val,(I.model.right e).val,I.model.weight e)) := by
  change entries (fullList (tape I).1,
    QuantumRoutingFamily.coarse (spatialDensity A D) (27*spatialDensity A D)
      (QuantumForkRoutingData.value (tape I))) = _
  rw [QuantumSpatialInputTape.state_eq,QuantumSpatialInputTape.routing_eq]
  have hp : QuantumRoutingFamily.coarse (spatialDensity A D) (27*spatialDensity A D)
      (QuantumRoutingInputProgram.actualData I.model (Equiv.refl _)) =
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support) :=
    QuantumRoutingFamily.coarse_actual I.model (Equiv.refl _) hA I.model_degree
  rw [hp]
  calc
    _ = entries (List.ofFn (fun e : I.model.Term =>
        ((I.model.left e).val,(I.model.right e).val,I.model.weight e)),
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support)) :=
      congrArg (fun bs => entries (bs,
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support)))
        (bonds_ofFn I)
    _ = _ := by
      refine (entries_ofFn (m := (fullList I.state).length)
        (fun e => ((I.model.left e).val,(I.model.right e).val,I.model.weight e))
        (fun e => (I.model.bufferedPath I.model_degree e).val.support)).trans ?_
      apply congrArg List.ofFn
      funext e
      apply Prod.ext
      · simp only [SimpleGraph.Walk.length_support,Nat.add_sub_cancel]
        rfl
      · rfl

theorem positions_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).2.1 =
      List.ofFn (fun v : Fin I.model.n => qmaExpandedPoint (I.model.placedVertex v)) := by
  change (QuantumRoutingFamily.positions (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (tape I))).map qmaExpandedPoint = _
  rw [QuantumSpatialInputTape.routing_eq]
  have hp : QuantumRoutingFamily.positions (spatialDensity A D) (27*spatialDensity A D)
      (QuantumRoutingInputProgram.actualData I.model (Equiv.refl _)) =
        List.ofFn I.model.placedVertex :=
    QuantumRoutingFamily.positions_actual I.model (Equiv.refl _)
  rw [hp,List.map_ofFn]
  rfl

include hA in
theorem paths_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).2.2 =
      List.ofFn (fun e : I.model.Term =>
        (List.range (2*I.model.coarseLength I.model_degree e+2)).map
          (qmaPortChain (I.model.coarseRoute I.model_degree e)
            (I.model.coarseLength I.model_degree e))) := by
  change QuantumPortChainProgram.allRouted (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (tape I)) = _
  rw [QuantumSpatialInputTape.routing_eq]
  exact allRouted_actual I.model (Equiv.refl _) hA I.model_degree

end ContinuumCoulomb.QuantumPortScheduleActual

end

end OAI
