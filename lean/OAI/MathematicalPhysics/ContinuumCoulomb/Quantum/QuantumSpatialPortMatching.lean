import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPortProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteMatching

namespace OAI

/-! Exact geometric matching for the actual spatial compiler. Its position
tape is a permutation of the canonical completed port graph. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialPortProgram
open QuantumForkList
open scoped Classical

theorem port_layout_matches {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ} (labels : M.Term ≃ Fin m)
    (hA : 0<A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (N : ℚ) (k : ℕ) (s : QuantumListRouteProgram.State)
    (hs : s=QuantumPackedSchedule.layout M.exchangeGraph labels
      (M.coarseLength hd) (M.portEmbedding hA hd)) :
    ∃ (hk : QuantumListSchedule.Valid (QuantumListRouteProgram.iterate N k s).1)
      (Pk : QMAPathEmbedding
        (QuantumListSchedule.schedule (QuantumListRouteProgram.iterate N k s).1 hk)
        ((M.portRouteData hA hd).graph))
      (Ek : QMAPathRelabeling
        (QuantumListSchedule.schedule (QuantumListRouteProgram.iterate N k s).1 hk)
        ((M.portRouteData hA hd).schedule.iterate N k)),
      QuantumListRouteProgram.Represents (QuantumListRouteProgram.iterate N k s) hk Pk ∧
      (∀ v, ((M.portEmbedding hA hd).iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, ((M.portEmbedding hA hd).iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  exact QuantumListRouteProgram.packed_matches_of_eq M.exchangeGraph labels
    (M.coarseLength hd) (M.portEmbedding hA hd) N k s hs

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)
include hA

theorem value_matches (N : ℚ) :
    ∃ (hk : QuantumListSchedule.Valid (value A D (N,QuantumSpatialInputTape.input I)).1)
      (Pk : QMAPathEmbedding
        (QuantumListSchedule.schedule (value A D (N,QuantumSpatialInputTape.input I)).1 hk)
        ((I.model.portRouteData hA I.model_degree).graph))
      (Ek : QMAPathRelabeling
        (QuantumListSchedule.schedule (value A D (N,QuantumSpatialInputTape.input I)).1 hk)
        ((I.model.portRouteData hA I.model_degree).schedule.iterate N (rounds A D))),
      QuantumListRouteProgram.Represents (value A D (N,QuantumSpatialInputTape.input I)) hk Pk ∧
      (∀ v, ((I.model.portEmbedding hA I.model_degree).iterate N (rounds A D)).position
          (Ek.vertex v) = Pk.position v) ∧
      (∀ e j, ((I.model.portEmbedding hA I.model_degree).iterate N (rounds A D)).point
          (Ek.edge e) j = Pk.point e j) := by
  have hi : initial A D (QuantumSpatialInputTape.input I)=
      QuantumPackedSchedule.layout I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) (I.model.portEmbedding hA I.model_degree) :=
    QuantumPortSchedulePacking.layout_eq I hA
  exact port_layout_matches I.model (Equiv.refl _) hA I.model_degree N (rounds A D)
    (initial A D (QuantumSpatialInputTape.input I)) hi

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
