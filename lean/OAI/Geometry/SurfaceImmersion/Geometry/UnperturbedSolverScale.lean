import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveData
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartBounds
import OAI.Geometry.SurfaceImmersion.Correction.CompactMeanBudgets

namespace OAI

/-! A fixed geometric metric solver works at every smaller slow scale.
Its geometry and coefficient profiles do not depend on the frequency. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean SmallModes

lemma phaseChartPolynomialOperator_zero {n : ℕ} {U : Set Base} {O : Set LowJet}
    {G : Base → Space} (hO : IsOpen O) (hU : IsOpen U)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source) :
    phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ 0 e he hi hKe = 0 := by
  have hz : tensorConjugatedLM hO hU P hP hG hQ K hKU hφ τ 0 0 = 0 := by
    ext Z x k
    simp [tensorConjugatedLM,tupleSupportedLM,conjugatedLM]
    rfl
  simp only [phaseChartPolynomialOperator,phaseCoordinatePolynomialOperator,hz,
    transportSupportedLM,chartTensorTransportLM,LinearMap.zero_comp,LinearMap.comp_zero]

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ} {K : Compacts Base}

/-- Only the numerical scale changes; the actual chart and inverse are fixed. -/
def atUnperturbedScale (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : PolynomialSolveData P 0 G hG φ K τ s where
  U := c.U
  O := c.O
  openU := c.openU
  openO := c.openO
  smoothP := c.smoothP
  mapsG := c.mapsG
  supportU := c.supportU
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
  coefficients := fun m => reconstruction_shrink_scale (c.coefficients m) s.coe_nonneg hs
  polynomial := by
    intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp only [LinearMap.zero_apply,map_zero,zero_div,zero_mul,le_refl]

@[simp] lemma atUnperturbedScale_e (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : (c.atUnperturbedScale τ s hs).e = c.e := rfl

@[simp] lemma atUnperturbedScale_C (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : (c.atUnperturbedScale τ s hs).C = c.C := rfl

@[simp] lemma atUnperturbedScale_J (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : (c.atUnperturbedScale τ s hs).J = c.J := rfl

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
