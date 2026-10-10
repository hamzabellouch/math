import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellRouteSupport

namespace OAI

/-! The actual merged-output route uses the finite 140-element catalog search. -/

namespace ContinuumCoulomb

theorem qmaInternalBody_cell (p : ℕ × ℕ) (e : QMAInternalEdge) :
    (qmaInternalBody p e).cell = p := by
  rcases e with a | (a | a) <;> rfl

noncomputable section
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem mergedOutputRoute_find (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) :
    P.findMergedRoute N hD e = some (P.mergedOutputRoute N hD havoid e) :=
  (Option.some_get (P.findMergedRoute_isSome N hD havoid e)).symm

end QMAPortRouteData
end
end ContinuumCoulomb

end OAI
