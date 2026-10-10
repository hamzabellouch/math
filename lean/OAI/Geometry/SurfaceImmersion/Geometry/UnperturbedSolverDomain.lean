import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverScale

namespace OAI

/-! Restrict the coefficient domain without changing an unperturbed phase solver. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ} {s : ℝ≥0}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ} {K : Compacts Base}

/-- Only the domain in which the polynomial coefficients are read changes.
The phase chart, reconstruction bounds and every numeric profile are retained. -/
def onDomain (c : PolynomialSolveData P 0 G hG φ K τ s)
    (U : Set Base) (hU : IsOpen U) (hUc : U ⊆ c.U) (hKU : (K : Set Base) ⊆ U) :
    PolynomialSolveData P 0 G hG φ K τ s where
  U := U
  O := c.O
  openU := hU
  openO := c.openO
  smoothP := c.smoothP
  mapsG := fun x hx => c.mapsG (hUc hx)
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
  D := c.D
  J := c.J
  nonnegC := c.nonnegC
  nonnegD := c.nonnegD
  oneLEJ := c.oneLEJ
  coordinates := c.coordinates
  coefficients := c.coefficients
  polynomial := by
    intro m Z
    have hz := phaseChartPolynomialOperator_zero c.openO hU P c.smoothP hG
      (fun x hx => c.mapsG (hUc hx)) K hKU c.smoothPhase τ c.e c.smoothForward
      c.smoothInverse c.supportChart
    rw [hz]
    simp

@[simp] lemma onDomain_e (c : PolynomialSolveData P 0 G hG φ K τ s)
    (U : Set Base) (hU : IsOpen U) (hUc : U ⊆ c.U) (hKU : (K : Set Base) ⊆ U) :
    (c.onDomain U hU hUc hKU).e = c.e := rfl

@[simp] lemma onDomain_U (c : PolynomialSolveData P 0 G hG φ K τ s)
    (U : Set Base) (hU : IsOpen U) (hUc : U ⊆ c.U) (hKU : (K : Set Base) ⊆ U) :
    (c.onDomain U hU hUc hKU).U = U := rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
