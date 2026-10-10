import OAI.MeasureTheory.Falconer.Estimates.RootLeibnizBounds
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def rootLeftSymbol (d : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) : Plane → UnitCircle → ℂ :=
  d.symbol N sig (fun b => k (.inl b)) (fun _ => 1)

noncomputable def rootRightSymbol (e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) : Plane → UnitCircle → ℂ :=
  e.symbol N sig (fun b => k (.inr b)) (fun _ => 1)

theorem rootLeftSymbol_measurable (d : RootEndpointData) (N : ℕ) (sig : ℝ) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => rootLeftSymbol d N sig k z.1 z.2) :=
  d.symbol_measurable N sig _

theorem rootRightSymbol_measurable (e : RootEndpointData) (N : ℕ) (sig : ℝ) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => rootRightSymbol e N sig k z.1 z.2) :=
  e.symbol_measurable N sig _

theorem rootLeftSymbol_norm (d e : RootEndpointData) (hd : 0 < d.Q.side) (N j : ℕ) (sig : ℝ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e))
    (x : Plane) (dir : UnitCircle) :
    ‖rootLeftSymbol d N sig b.2 x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  d.symbol_norm hd N sig _ (2*j)
    (root_assignment_budgets d e _ _ (inverseLeibnizTerms_budget j _ hb)).1 x dir

theorem rootRightSymbol_norm (d e : RootEndpointData) (he : 0 < e.Q.side) (N j : ℕ) (sig : ℝ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e))
    (y : Plane) (dir : UnitCircle) :
    ‖rootRightSymbol e N sig b.2 y dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  e.symbol_norm he N sig _ (2*j)
    (root_assignment_budgets d e _ _ (inverseLeibnizTerms_budget j _ hb)).2 y dir

theorem root_inverseCircleOperator_terms (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (j : ℕ) (dir : UnitCircle) :
    inverseCircleOperator j (rootPairSymbol d e N sig z) dir =
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
        b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
          (rootLeftSymbol d N sig b.2 z.1 dir * conj (rootRightSymbol e N sig b.2 z.2 dir))))).sum := by
  simpa only [inverseCircleOperator,sourceUnitDirection_sourceAngle,rootLeftSymbol,rootRightSymbol] using
    rootPairSymbol_inverse_leibniz d e hd he N sig z j (sourceAngle dir)

end PlanarFalconer

end OAI
