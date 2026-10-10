import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPatchEdgeCover
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPatchChart

namespace OAI

/-! Every edge of the actual simultaneous crossing output has a short permitted
lattice route with the exact physical endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev crossingOutput (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :=
  (P.portCrossingSelection N hD).layer.output N

theorem crossingOutput_route_exists (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).Edge) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D ((P.crossingOutput N hD).left e) ∧
      R.target = P.crossingPosition N D ((P.crossingOutput N hD).right e) := by
  rcases qmaCrossingsEdge_cover e with ⟨f,rfl⟩ | ⟨i,k,rfl⟩
  · let R := P.retainedRoute N hD havoid f
    have hs := P.retainedRoute_spec N hD havoid f
    refine ⟨R,hs.1,hs.2.1,?_,?_⟩
    · change R.source = P.crossingPosition N D
        (old (P.finishedGraph N D).n P.crossingCells.card ((P.finishedGraph N D).left f.val))
      rw [P.crossingPosition_old]
      exact hs.2.2.1
    · change R.target = P.crossingPosition N D
        (old (P.finishedGraph N D).n P.crossingCells.card ((P.finishedGraph N D).right f.val))
      rw [P.crossingPosition_old]
      exact hs.2.2.2
  · refine ⟨qmaPatchRoute (P.crossingCell i).val k,?_,trivial,?_,?_⟩
    · exact P.mem_crossingCells.mp (P.crossingCell i).property
    · rw [qmaPatchRoute_source]
      change _ = P.crossingPosition N D
        (qmaParallelGraphLeft (qmaCrossingsBaseLeft (P.portCrossingSelection N hD).retained.left
          (P.crossingSiteFin N hD)) (P.crossingSiteFin N hD) (qmaPatchPhysicalEdge i k))
      rw [qmaPatchPhysical_left]
      exact (P.crossingPosition_patchVertex N hD i (qmaPatchSource k)).symm
    · rw [qmaPatchRoute_target]
      change _ = P.crossingPosition N D
        (qmaParallelGraphRight (qmaCrossingsBaseRight (P.portCrossingSelection N hD).retained.right
          (P.crossingSiteFin N hD)) (fun _ => qmaCrossingMember) (qmaPatchPhysicalEdge i k))
      rw [qmaPatchPhysical_right]
      exact (P.crossingPosition_patchVertex N hD i (qmaPatchTarget k)).symm

def crossingOutputRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).Edge) : QMACellRoute :=
  Classical.choose (P.crossingOutput_route_exists N hD havoid e)

theorem crossingOutputRoute_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).Edge) :
    P.RoutingAllowed (P.crossingOutputRoute N hD havoid e).body ∧
    (P.crossingOutputRoute N hD havoid e).Valid ∧
    (P.crossingOutputRoute N hD havoid e).source =
      P.crossingPosition N D ((P.crossingOutput N hD).left e) ∧
    (P.crossingOutputRoute N hD havoid e).target =
      P.crossingPosition N D ((P.crossingOutput N hD).right e) :=
  Classical.choose_spec (P.crossingOutput_route_exists N hD havoid e)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
