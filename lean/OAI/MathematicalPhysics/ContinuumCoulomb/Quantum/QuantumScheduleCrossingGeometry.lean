import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumComputedCrossingRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPositionRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSiteRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergedSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabeling
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingOutputRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPacketGeometry

namespace OAI

/-! Match the complete literal crossing packet to the canonical port crossing
geometry. The input schedule and the crossing cells may have arbitrary orders. -/

noncomputable section
namespace ContinuumCoulomb.QuantumScheduleCrossingGeometry
open QuantumCrossingSelectProgram QuantumCrossingListLayer
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (s : QuantumListSchedule.State) (hs : QuantumListSchedule.Valid s)
    (E : QMAPathRelabeling (QuantumListSchedule.schedule s hs) (P.schedule.iterate N D))
    {r : ℕ} (cell : Fin r ≃ Fin P.crossingCells.card)

def site (i : Fin r) (a : Fin 4) : Fin s.1 :=
  E.vertex.symm (P.crossingSiteFin N hD (cell i) a)

theorem site_global : Function.Injective (fun p : Fin r × Fin 4 => site P N hD s hs E cell p.1 p.2) :=
  QuantumCrossingSiteProgram.reordered_sites_global P N hD E.vertex cell

theorem site_injective (i : Fin r) : Function.Injective (site P N hD s hs E cell i) := by
  intro a b hab
  exact congrArg Prod.snd (site_global P N hD s hs E cell (a₁ := (i,a)) (a₂ := (i,b)) hab)

def layer : QMARationalCrossingLayer r :=
  computedLayer ((QuantumListSchedule.graph s hs).crossingSelection
    (site P N hD s hs E cell) (site_injective P N hD s hs E cell)) (Equiv.refl _)

def input : QuantumCrossingListLayer.Input :=
  QuantumCrossingSelectProgram.value (N,(s.1,QuantumListSchedule.erase s.2.2,s.2.1),
    List.ofFn (encodedSites (site P N hD s hs E cell)))

theorem input_actual : input P N hD s hs E cell =
    actualInput (layer P N hD s hs E cell) N (Equiv.refl _) := by
  have h := compiled_packet ((QuantumListSchedule.graph s hs).crossingSelection
    (site P N hD s hs E cell) (site_injective P N hD s hs E cell)) (Equiv.refl _) N
  have hp := congrArg (fun bs => QuantumCrossingSelectProgram.value
    (N,(s.1,bs,s.2.1),List.ofFn (encodedSites (site P N hD s hs E cell))))
      (QuantumListSchedule.graph_packed s hs).symm
  exact hp.trans h

def vertex : Fin (actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).n ≃
    Fin (P.crossingOutput N hD).n :=
  (actualVertex (layer P N hD s hs E cell) N (Equiv.refl _)).trans
    ((layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer E.vertex cell)

theorem layer_support :
    (∀ e : ((layer P N hD s hs E cell).output N).Edge,
      ∃ f : (P.crossingOutput N hD).Edge,
        s((layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).left e),
          (layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) ∧
    (∀ f : (P.crossingOutput N hD).Edge,
      ∃ e : ((layer P N hD s hs E cell).output N).Edge,
        s((layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).left e),
          (layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) := by
  exact computed_output_support E.vertex E.edge E.left E.right
    (site P N hD s hs E cell) (P.crossingSiteFin N hD) cell
    (fun _ _ => E.vertex.apply_symm_apply _) (site_injective P N hD s hs E cell)
    (P.crossingSiteFin_injective N hD) (site_global P N hD s hs E cell) (Equiv.refl _) N N

theorem output_support :
    (∀ e : (actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).Edge,
      ∃ f : (P.crossingOutput N hD).Edge,
        s(vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).left e),
          vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) ∧
    (∀ f : (P.crossingOutput N hD).Edge,
      ∃ e : (actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).Edge,
        s(vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).left e),
          vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) := by
  let C := layer P N hD s hs E cell
  let V := C.vertexRelabel (P.portCrossingSelection N hD).layer E.vertex cell
  have hl := layer_support P N hD s hs E cell
  constructor
  · intro e
    obtain ⟨k,hk⟩ := actual_support_source C N (Equiv.refl _) e
    obtain ⟨f,hf⟩ := hl.1 k
    exact ⟨f,(qmaUnorderedPair_map V hk).trans hf⟩
  · intro f
    obtain ⟨k,hk⟩ := hl.2 f
    obtain ⟨e,he⟩ := actual_support_target C N (Equiv.refl _) k
    exact ⟨e,(qmaUnorderedPair_map V he).trans hk⟩

theorem positions_actual :
    QuantumCrossingPositionProgram.positions
      (List.ofFn (fun i => (P.crossingCell (cell i)).val),
        List.ofFn (fun v => P.finishedPosition N D (E.vertex v))) =
      List.ofFn (fun v => P.crossingPosition N D (vertex P N hD s hs E cell v)) := by
  let C := layer P N hD s hs E cell
  have hp := QuantumCrossingPositionProgram.positions_reordered P N D E.vertex cell
  apply hp.trans
  exact List.ofFn_congr (count_actual C N (Equiv.refl _)).symm
    (fun v => P.crossingPosition N D (C.vertexRelabel (P.portCrossingSelection N hD).layer E.vertex cell v))

theorem packet_geometry : QMAPacketGeometry (P.crossingOutput N hD)
    (P.crossingPosition N D) (QuantumCrossingListLayer.value (input P N hD s hs E cell))
    (QuantumCrossingPositionProgram.positions
      (List.ofFn (fun i => (P.crossingCell (cell i)).val),
        List.ofFn (fun v => P.finishedPosition N D (E.vertex v)))) := by
  rw [input_actual]
  let C := layer P N hD s hs E cell
  refine ⟨bonds_bounded _ (QuantumListGraph.packed_bounded C.base (Equiv.refl _))
    (sites_bounded C N (Equiv.refl _)),
    bonds_noLoops _ (QuantumListGraph.packed_noLoops C.base (Equiv.refl _))
      (sites_bounded C N (Equiv.refl _)) (sites_injective C N (Equiv.refl _)),?_⟩
  exact ⟨vertex P N hD s hs E cell,positions_actual P N hD s hs E cell,
    output_support P N hD s hs E cell⟩

end ContinuumCoulomb.QuantumScheduleCrossingGeometry

end

end OAI
