import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergedOutputRoutes

namespace OAI

/-! Distinct merged interactions have different unordered physical endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaMergedEndpointPairs_injective (G : QMARationalExchangeGraph)
    (position : Fin G.n → ℕ × ℕ) (hp : Function.Injective position) :
    Function.Injective (fun e : G.merge.Edge => s(position (G.merge.left e),position (G.merge.right e))) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact G.merge_pair_injective (Prod.ext (hp hl) (hp hr))
  · have hleft := hp hl
    have hright := hp hr
    have he := G.mergedEdge_lt e
    have hf := G.mergedEdge_lt f
    change G.merge.left e < G.merge.right e at he
    change G.merge.left f < G.merge.right f at hf
    rw [hleft,hright] at he
    exact (lt_asymm he hf).elim

namespace QMACellRoute

def endpointPair (R : QMACellRoute) : Sym2 (ℕ × ℕ) := s(R.source,R.target)

theorem endpointPair_body (R : QMACellRoute) : R.endpointPair = s(R.body.source,R.body.target) := by
  rcases R with ⟨b,r⟩
  cases r
  · rfl
  · exact Sym2.eq_swap

end QMACellRoute
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem mergedOutputRoute_pairs_injective (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v) :
    Function.Injective (fun e => (P.mergedOutputRoute N hD havoid e).endpointPair) := by
  intro e f h
  apply qmaMergedEndpointPairs_injective (P.crossingOutput N hD)
    (P.crossingPosition N D) (P.crossingPosition_injective N D)
  have he := P.mergedOutputRoute_spec N hD havoid e
  have hf := P.mergedOutputRoute_spec N hD havoid f
  simpa only [QMACellRoute.endpointPair,he.2.2.1,he.2.2.2,hf.2.2.1,hf.2.2.2] using h

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
