import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortScheduleTape
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabelingProperties

namespace OAI

/-! Packing a finite exchange graph with a work counter retains its endpoints
and work exactly. This bridges the literal schedule to the geometric one. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule
open QuantumListSchedule
open scoped Classical

theorem schedule_congr {s t : State} (h : s=t) (hs : Valid s) (ht : Valid t) :
    schedule s hs=schedule t ht := by
  cases h
  rfl

def state (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : State :=
  (G.n,G.constant,List.ofFn (fun i => (work (labels.symm i),
    (G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i))))

theorem erase_state (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : erase (state G labels work).2.2=QuantumListGraph.packed G labels := by
  simp only [erase,state,List.map_ofFn,QuantumListGraph.packed,Function.comp_def]

theorem valid (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : Valid (state G labels work) := by
  constructor
  · rw [erase_state]
    exact QuantumListGraph.packed_bounded G labels
  · rw [erase_state]
    exact QuantumListGraph.packed_noLoops G labels

def scheduleRelabel (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) :
    QMAPathRelabeling (schedule (state G labels work) (valid G labels work)) ⟨G,work⟩ where
  vertex := Equiv.refl _
  edge := (finCongr (show (state G labels work).2.2.length = m from List.length_ofFn)).trans labels.symm
  left := by
    intro e
    apply Fin.ext
    simp only [schedule,graph,state,List.get_eq_getElem,List.getElem_ofFn]
    rfl
  right := by
    intro e
    apply Fin.ext
    simp only [schedule,graph,state,List.get_eq_getElem,List.getElem_ofFn]
    rfl
  work := by
    intro e
    change ((List.ofFn (fun i : Fin m => (work (labels.symm i),
      (G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i)))).get e).1 = _
    exact (congrArg Prod.fst (List.get_ofFn
      (fun i : Fin m => (work (labels.symm i),
        (G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i))) e))

theorem energy (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : QuantumListSchedule.energy (state G labels work)=G.energy := by
  unfold QuantumListSchedule.energy
  rw [erase_state]
  exact congrArg (sourceMatrixBottom G.n) (QuantumListGraph.packed_matrix G labels)

def layout (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) :
    QuantumListRouteProgram.State :=
  (state G labels work,List.ofFn P.position,List.ofFn (fun i : Fin m =>
    (List.range (2*work (labels.symm i)+2)).map (P.point (labels.symm i))))

theorem layout_represents (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) :
    QuantumListRouteProgram.Represents (layout G labels work P) (valid G labels work)
      ((scheduleRelabel G labels work).symm.transport P) := by
  constructor
  · rfl
  · apply List.ext_getElem
    · simp only [layout,List.length_ofFn,schedule,graph,state]
    · intro i hi hj
      have hi' : i < m := by simpa only [layout,List.length_ofFn] using hi
      simp only [layout,List.getElem_ofFn]
      have hw := (scheduleRelabel G labels work).work
        (⟨i,by simpa only [state,List.length_ofFn] using hi'⟩ :
          (schedule (state G labels work) (valid G labels work)).graph.Edge)
      rw [hw]
      rfl

theorem layout_has_representation (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ) {Γ : SimpleGraph (ℕ × ℕ)}
    (P : QMAPathEmbedding ⟨G,work⟩ Γ) {X Y : ℕ} (hb : P.Bounded X Y) :
    ∃ (hs : QuantumListSchedule.Valid (layout G labels work P).1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule (layout G labels work P).1 hs) Γ),
      QuantumListRouteProgram.Represents (layout G labels work P) hs Q ∧ Q.Bounded X Y :=
  ⟨valid G labels work,_,layout_represents G labels work P,
    (scheduleRelabel G labels work).symm.transport_bounded P hb⟩

end ContinuumCoulomb.QuantumPackedSchedule

end

end OAI
