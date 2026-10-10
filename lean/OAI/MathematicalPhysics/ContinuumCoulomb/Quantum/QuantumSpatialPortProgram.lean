import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortSchedulePacking
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRoutePreservation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortRealization

namespace OAI

/-! Literal fixed-round realization of the computed spatial graph on its port
paths. The finite tape carries the actual spin positions throughout subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialPortProgram
open ExactQuantumFactoring.BitStackProgram QuantumForkList QuantumRouteCode

abbrev Input := ℚ × QuantumForkGridProgram.PreparedInput
def inputCode : Input → List Bool := prodCode ratCode QuantumForkGridProgram.preparedCode

def initial (A D : ℕ) (x : QuantumForkGridProgram.PreparedInput) :
    QuantumListRouteProgram.State :=
  QuantumPortScheduleTape.value (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkGridProgram.output D x)

private opaque roundValue (A D : ℕ) : { k : ℕ //
    QMASpatialExchangeModel.routeLengthBound (spatialDensity A D) (27*spatialDensity A D)=k } :=
  ⟨QMASpatialExchangeModel.routeLengthBound (spatialDensity A D) (27*spatialDensity A D),rfl⟩
def rounds (A D : ℕ) : ℕ := (roundValue A D).val
theorem rounds_eq (A D : ℕ) :
    QMASpatialExchangeModel.routeLengthBound (spatialDensity A D) (27*spatialDensity A D)=
      rounds A D := (roundValue A D).property

def value (A D : ℕ) (x : Input) : QuantumListRouteProgram.State :=
  QuantumListRouteProgram.iterate x.1 (rounds A D) (initial A D x.2)

noncomputable opaque initialProgram (A D : ℕ) :
    Procedure QuantumForkGridProgram.preparedCode QuantumListRouteProgram.stateCode
      (initial A D) :=
  (QuantumPortScheduleTape.program (spatialDensity A D) (27*spatialDensity A D)).comp
    (QuantumForkGridProgram.outputProgram D)

noncomputable opaque program (A D : ℕ) :
    Procedure inputCode QuantumListRouteProgram.stateCode (value A D) :=
  (QuantumListRouteProgram.iterateProgram (rounds A D)).comp
    ((Procedure.first ratCode QuantumForkGridProgram.preparedCode).pair
      ((initialProgram A D).comp (Procedure.second ratCode QuantumForkGridProgram.preparedCode)))

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)
include hA

theorem initial_bounded :
    ∃ (hs : QuantumListSchedule.Valid (initial A D (QuantumSpatialInputTape.input I)).1)
      (P : QMAPathEmbedding
        (QuantumListSchedule.schedule (initial A D (QuantumSpatialInputTape.input I)).1 hs)
        (I.model.portGraph I.model_degree)),
      QuantumListRouteProgram.Represents (initial A D (QuantumSpatialInputTape.input I)) hs P ∧
      P.Bounded (32*I.model.bufferedWidth) (32*I.model.bufferedHeight) := by
  obtain ⟨hs,P,hP⟩ := QuantumPortSchedulePacking.has_representation I hA
  refine ⟨hs,P,hP,QuantumListRouteProgram.bounded_of_lists _ hs P hP ?_ ?_⟩
  · intro p hp
    change p ∈ (QuantumPortScheduleTape.value _ _ (QuantumPortScheduleActual.tape I)).2.1 at hp
    rw [QuantumPortScheduleActual.positions_actual I] at hp
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hp
    exact qmaExpandedPoint_bounds (I.model.placedVertex_bounds v).1
      (I.model.placedVertex_bounds v).2
  · intro ps hps p hp
    change ps ∈ (QuantumPortScheduleTape.value _ _ (QuantumPortScheduleActual.tape I)).2.2 at hps
    rw [QuantumPortScheduleActual.paths_actual I hA] at hps
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hps
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact qmaPortChain_bounds (I.model.coarseRoute I.model_degree e)
      (fun i _ => I.model.bufferedPath_bounds I.model_degree e
        ((I.model.bufferedPath I.model_degree e).val.getVert_mem_support i)) k
      (by have := List.mem_range.mp hk; omega)

theorem initial_work : ∀ e ∈ (initial A D (QuantumSpatialInputTape.input I)).1.2.2,
    e.1 ≤ rounds A D := by
  intro e he
  change e ∈ (QuantumPortScheduleTape.value _ _ (QuantumPortScheduleActual.tape I)).1.2.2 at he
  rw [QuantumPortScheduleActual.entries_actual I hA] at he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  rw [← rounds_eq]
  exact I.model.bufferedPath_length I.model_degree i

theorem realizes {N : ℚ} (hN : 0 < N) :
    ∃ (hs : QuantumListSchedule.Valid (value A D (N,QuantumSpatialInputTape.input I)).1)
      (P : QMAPathEmbedding
        (QuantumListSchedule.schedule (value A D (N,QuantumSpatialInputTape.input I)).1 hs)
        (I.model.portGraph I.model_degree)),
      QuantumListRouteProgram.Represents (value A D (N,QuantumSpatialInputTape.input I)) hs P ∧
      P.Bounded (32*I.model.bufferedWidth) (32*I.model.bufferedHeight) ∧
      (∀ e, (I.model.portGraph I.model_degree).Adj
        (P.position ((QuantumListSchedule.schedule _ hs).graph.left e))
        (P.position ((QuantumListSchedule.schedule _ hs).graph.right e))) ∧
      (value A D (N,QuantumSpatialInputTape.input I)).1.1+
        (value A D (N,QuantumSpatialInputTape.input I)).1.2.2.length ≤
        5^(rounds A D)*((initial A D (QuantumSpatialInputTape.input I)).1.1+
          (initial A D (QuantumSpatialInputTape.input I)).1.2.2.length) ∧
      |QuantumListSchedule.energy (value A D (N,QuantumSpatialInputTape.input I)).1-
        I.model.energy| ≤ (rounds A D:ℝ)/(N:ℝ) := by
  obtain ⟨hs,P,hP,hbox⟩ := initial_bounded I hA
  obtain ⟨hs',Q,hQ,hQbox,hadj,hsize,henergy⟩ :=
    QuantumListRouteProgram.compile_realization hN _ hs P hP (initial_work I hA) hbox
  refine ⟨hs',Q,hQ,hQbox,hadj,hsize,?_⟩
  exact (QuantumPortSchedulePacking.energy I hA) ▸ henergy

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
