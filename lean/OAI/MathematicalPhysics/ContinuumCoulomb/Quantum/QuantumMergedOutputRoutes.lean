import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingOutputRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergeEdges
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteEnumeration

namespace OAI

/-! Exact parallel-edge merging preserves the physical placement and reverses
the catalog route when canonical endpoint ordering requires it. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMACellRoute

def reverse (R : QMACellRoute) : QMACellRoute := ⟨R.body,!R.reversed⟩

@[simp] theorem reverse_body (R : QMACellRoute) : R.reverse.body = R.body := rfl

@[simp] theorem reverse_source (R : QMACellRoute) : R.reverse.source = R.target := by
  rcases R with ⟨b,r⟩
  cases r <;> rfl

@[simp] theorem reverse_target (R : QMACellRoute) : R.reverse.target = R.source := by
  rcases R with ⟨b,r⟩
  cases r <;> rfl

@[simp] theorem reverse_valid (R : QMACellRoute) : R.reverse.Valid = R.Valid := rfl

end QMACellRoute
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem mergedOutput_route_exists (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D ((P.crossingOutput N hD).merge.left e) ∧
      R.target = P.crossingPosition N D ((P.crossingOutput N hD).merge.right e) := by
  obtain ⟨f,hf⟩ := (P.crossingOutput N hD).merge_edge_source e
  obtain ⟨R,hR,hv,hl,hr⟩ := P.crossingOutput_route_exists N hD havoid f
  rcases hf with ⟨hleft,hright⟩ | ⟨hleft,hright⟩
  · exact ⟨R,hR,hv,hl.trans (congrArg (P.crossingPosition N D) hleft.symm),
      hr.trans (congrArg (P.crossingPosition N D) hright.symm)⟩
  · refine ⟨R.reverse,hR,hv,?_,?_⟩
    · exact R.reverse_source.trans (hr.trans (congrArg (P.crossingPosition N D) hleft.symm))
    · exact R.reverse_target.trans (hl.trans (congrArg (P.crossingPosition N D) hright.symm))

def findMergedRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.crossingOutput N hD).merge.Edge) : Option QMACellRoute :=
  (qmaRouteCandidates
    (P.crossingPosition N D ((P.crossingOutput N hD).merge.left e))
    (P.crossingPosition N D ((P.crossingOutput N hD).merge.right e))).find? (fun R =>
      decide (P.RoutingAllowed R.body ∧ R.Valid ∧
        R.source = P.crossingPosition N D ((P.crossingOutput N hD).merge.left e) ∧
        R.target = P.crossingPosition N D ((P.crossingOutput N hD).merge.right e)))

theorem findMergedRoute_isSome (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) : (P.findMergedRoute N hD e).isSome := by
  obtain ⟨R,hR,hvalid,hs,ht⟩ := P.mergedOutput_route_exists N hD havoid e
  apply List.find?_isSome.mpr
  refine ⟨R,?_,?_⟩
  · simpa only [hs,ht] using qmaRouteCandidates_complete R
  · exact decide_eq_true ⟨hR,hvalid,hs,ht⟩

theorem findMergedRoute_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.crossingOutput N hD).merge.Edge) {R : QMACellRoute}
    (h : P.findMergedRoute N hD e = some R) :
    P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D ((P.crossingOutput N hD).merge.left e) ∧
      R.target = P.crossingPosition N D ((P.crossingOutput N hD).merge.right e) := by
  unfold findMergedRoute at h
  have hp := List.find?_some h
  exact of_decide_eq_true hp


def mergedOutputRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) : QMACellRoute :=
  (P.findMergedRoute N hD e).get (P.findMergedRoute_isSome N hD havoid e)

theorem mergedOutputRoute_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) :
    P.RoutingAllowed (P.mergedOutputRoute N hD havoid e).body ∧
    (P.mergedOutputRoute N hD havoid e).Valid ∧
    (P.mergedOutputRoute N hD havoid e).source =
      P.crossingPosition N D ((P.crossingOutput N hD).merge.left e) ∧
    (P.mergedOutputRoute N hD havoid e).target =
      P.crossingPosition N D ((P.crossingOutput N hD).merge.right e) := by
  apply P.findMergedRoute_spec N hD e
  exact (Option.some_get (P.findMergedRoute_isSome N hD havoid e)).symm

theorem mergedOutput_energy_error {N : ℚ} (hN : 0 < N) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    |(P.crossingOutput N hD).merge.energy-G.energy| ≤ ((D+1:ℕ):ℝ)/(N:ℝ) := by
  rw [QMARationalExchangeGraph.merge_energy]
  exact P.portCrossing_energy_error hN hD

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
