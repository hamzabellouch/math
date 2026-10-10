import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverFromBounds

namespace OAI

/-! Restrict the positional domain of an unperturbed supported solver.
Its phase chart, operator, and numerical coefficient budgets stay fixed. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

namespace PolynomialSolveData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}

def onSourceDomain (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (U : Set Base) (hU : IsOpen U) (hKU : (K : Set Base) ⊆ U) :
    PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s where
  U := U
  O := univ
  openU := hU
  openO := isOpen_univ
  smoothP := fun _ j => Fin.elim0 j
  mapsG := mapsTo_univ _ _
  supportU := hKU
  smoothPhase := c.smoothPhase
  e := c.e
  smoothForward := c.smoothForward
  smoothInverse := c.smoothInverse
  supportChart := c.supportChart
  phase := c.phase
  smoothMap := c.smoothMap
  domain := c.domain
  C := c.C
  D := fun _ => 0
  J := c.J
  nonnegC := c.nonnegC
  nonnegD := fun _ => le_rfl
  oneLEJ := c.oneLEJ
  coordinates := c.coordinates
  coefficients := c.coefficients
  polynomial := by
    intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
