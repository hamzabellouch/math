import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChainSeparation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutedSubdivision

namespace OAI

/-! Coarse paths may meet in cells, but disjoint grid edges give disjoint port chains. -/

noncomputable section
namespace ContinuumCoulomb

structure QMAPortRouteData (G : QMARationalExchangeGraph) where
  length : G.Edge → ℕ
  length_pos : ∀ e, 0 < length e
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : G.Edge → ℕ → ℕ × ℕ
  first : ∀ e, point e 0 = position (G.left e)
  last : ∀ e, point e (length e) = position (G.right e)
  simple : ∀ e i j, i ≤ length e → j ≤ length e → point e i = point e j → i = j
  step : ∀ e i, i < length e → qmaSquareGrid.Adj (point e i) (point e (i+1))
  positive : ∀ e i, i ≤ length e → 0 < (point e i).1 ∧ 0 < (point e i).2
  edges_disjoint : ∀ e f, e ≠ f → ∀ i j, i < length e → j < length f →
    ¬(point e i = point f j ∧ point e (i+1) = point f (j+1)) ∧
    ¬(point e i = point f (j+1) ∧ point e (i+1) = point f j)

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev schedule : QMAPathSchedule := ⟨G,P.length⟩

def graph : SimpleGraph (ℕ × ℕ) := SimpleGraph.fromRel (fun x y => ∃ (e : G.Edge) (k : ℕ),
  k < 2*P.length e+1 ∧ qmaPortChain (P.point e) (P.length e) k = x ∧
    qmaPortChain (P.point e) (P.length e) (k+1) = y)

def toEmbedding : QMAPathEmbedding P.schedule P.graph where
  position := fun v => qmaExpandedPoint (P.position v)
  position_injective := qmaExpandedPoint_injective.comp P.position_injective
  point := fun e => qmaPortChain (P.point e) (P.length e)
  first := by intro e; rw [qmaPortChain_zero,P.first]
  last := by intro e; change qmaPortChain (P.point e) (P.length e) (2*P.length e+1) = _
             rw [qmaPortChain_last,P.last]
  simple := by
    intro e i j hi hj h
    exact qmaPortChain_injective _ (P.length_pos e) (P.step e) (P.positive e) (P.simple e) hi hj h
  step := by
    intro e i hi
    change i < 2*P.length e+1 at hi
    apply (SimpleGraph.fromRel_adj _ _ _).mpr
    refine ⟨?_,Or.inl ⟨e,i,hi,rfl,rfl⟩⟩
    intro h
    have he := qmaPortChain_injective _ (P.length_pos e) (P.step e) (P.positive e) (P.simple e)
      (Nat.le_of_lt hi) (by omega) h
    omega
  avoids := by
    intro e i v hi0 hi
    exact qmaPortChain_inner_not_center _ hi0 hi _
  disjoint := by
    intro e f i j hef hi0 hi hj
    exact qmaPortChain_interiors_disjoint _ _ (P.step e) (P.step f) (P.positive e) (P.positive f)
      (P.edges_disjoint e f hef) hi0 hi hj

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
