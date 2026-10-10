import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPackedSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortScheduleActual
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortRealization

namespace OAI

/-! The actual computed scheduler begins with the exact spatial exchange
graph, with one work counter for each of its enumerated interactions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule

theorem port_layout {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    layout M.exchangeGraph labels (M.coarseLength hd) (M.portEmbedding hA hd) =
      (state M.exchangeGraph labels (M.coarseLength hd),
        List.ofFn (fun v => qmaExpandedPoint (M.placedVertex v)),
        List.ofFn (fun i : Fin m => (List.range (2*M.coarseLength hd (labels.symm i)+2)).map
          (qmaPortChain (M.coarseRoute hd (labels.symm i)) (M.coarseLength hd (labels.symm i))))) := by
  simp only [layout,QMASpatialExchangeModel.portEmbedding,
    QMASpatialExchangeModel.portRouteData,QMAPortRouteData.toEmbedding]

end ContinuumCoulomb.QuantumPackedSchedule

namespace ContinuumCoulomb.QuantumListRouteProgram

theorem bounded_of_lists {Γ : SimpleGraph (ℕ × ℕ)} (s : State)
    (hs : QuantumListSchedule.Valid s.1)
    (P : QMAPathEmbedding (QuantumListSchedule.schedule s.1 hs) Γ)
    (hP : Represents s hs P) {X Y : ℕ}
    (hv : ∀ p ∈ s.2.1, p.1 < X ∧ p.2 < Y)
    (he : ∀ ps ∈ s.2.2, ∀ p ∈ ps, p.1 < X ∧ p.2 < Y) : P.Bounded X Y := by
  constructor
  · intro v
    apply hv
    rw [hP.1]
    exact List.mem_ofFn.mpr ⟨v,rfl⟩
  · intro e k hk
    apply he ((List.range (2*(QuantumListSchedule.schedule s.1 hs).work e+2)).map (P.point e))
    · rw [hP.2]
      exact List.mem_ofFn.mpr ⟨e,rfl⟩
    · exact List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),rfl⟩

end ContinuumCoulomb.QuantumListRouteProgram

namespace ContinuumCoulomb.QuantumPortSchedulePacking
open QuantumForkList QuantumPortScheduleTape QuantumPortScheduleActual

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)
include hA

theorem state_eq :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 =
      QuantumPackedSchedule.state I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) := by
  apply Prod.ext
  · change (tape I).1.1=I.model.n
    rw [QuantumSpatialInputTape.state_eq]
    rfl
  · apply Prod.ext
    · change (tape I).1.2.2.1=I.model.constant
      rw [QuantumSpatialInputTape.state_eq]
      rfl
    · exact entries_actual I hA

theorem valid : QuantumListSchedule.Valid
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 := by
  rw [state_eq I hA]
  exact QuantumPackedSchedule.valid I.model.exchangeGraph (Equiv.refl _)
    (I.model.coarseLength I.model_degree)

theorem energy : QuantumListSchedule.energy
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 = I.model.energy := by
  rw [state_eq I hA]
  exact QuantumPackedSchedule.energy I.model.exchangeGraph (Equiv.refl _)
    (I.model.coarseLength I.model_degree)

theorem layout_eq :
    value (spatialDensity A D) (27*spatialDensity A D) (tape I) =
      QuantumPackedSchedule.layout I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) (I.model.portEmbedding hA I.model_degree) := by
  refine Eq.trans ?_ (QuantumPackedSchedule.port_layout I.model
    (m := (fullList I.state).length) (Equiv.refl _) hA I.model_degree).symm
  apply Prod.ext
  · exact state_eq I hA
  · apply Prod.ext
    · exact positions_actual I
    · exact paths_actual I hA

theorem has_representation :
    ∃ (hs : QuantumListSchedule.Valid
        (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1)
      (P : QMAPathEmbedding
        (QuantumListSchedule.schedule
          (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 hs)
        (I.model.portGraph I.model_degree)),
      QuantumListRouteProgram.Represents
        (value (spatialDensity A D) (27*spatialDensity A D) (tape I)) hs P := by
  rw [layout_eq I hA]
  exact ⟨QuantumPackedSchedule.valid _ _ _,_,
    QuantumPackedSchedule.layout_represents _ _ _ _⟩

end ContinuumCoulomb.QuantumPortSchedulePacking

end

end OAI
