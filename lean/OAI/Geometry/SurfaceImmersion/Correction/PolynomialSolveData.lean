import OAI.Geometry.SurfaceImmersion.Correction.GlobalChartedForcedMode

namespace OAI

/-! Geometric and quantitative data for the already constructed finite
polynomial phase solver. The operator bound here is supplied by
`phaseChartPolynomialOperator_bounds`; it concerns the actual transported
polynomial derivative. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

structure PolynomialSolveData {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) (G : Base → Space) (hG : ContDiff ℝ ∞ G)
    (φ : Base → ℝ) (K : Compacts Base) (τ : ℝ) (s : ℝ≥0) where
  U : Set Base
  O : Set LowJet
  openU : IsOpen U
  openO : IsOpen O
  smoothP : ∀ k l, (P k l).SmoothCoeffs O
  mapsG : Set.MapsTo (lowJet G) U O
  supportU : (K : Set Base) ⊆ U
  smoothPhase : ContDiff ℝ ∞ φ
  e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base
  smoothForward : ContDiffOn ℝ ∞ e e.source
  smoothInverse : ContDiffOn ℝ ∞ e.symm e.target
  supportChart : (modeSupport K : Set SmallModes.Base) ⊆ e.source
  phase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x
  smoothMap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm)
  domain : SmallModes.ModeDomain (fun p => RealModes.complexify
    (G (planeCoordinateIsometry.symm (e.symm p)))) e.target
  C : ℕ → ℝ
  D : ℕ → ℝ
  J : ℕ → ℝ
  nonnegC : ∀ m, 0 ≤ C m
  nonnegD : ∀ m, 0 ≤ D m
  oneLEJ : ∀ m, 1 ≤ J m
  coordinates : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
    ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m
  coefficients : ∀ m, SmallModes.ReconstructionCoefficientBound
    (fun p => RealModes.complexify (G (planeCoordinateIsometry.symm (e.symm p))))
    e.target s (m + 1) (C m)
  polynomial : ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) supportChart) s m
    (phaseChartPolynomialOperator openO openU P smoothP hG mapsG K supportU smoothPhase
      τ ε e smoothForward smoothInverse supportChart Z) ≤
    ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
      (chartSupport e (modeSupport K) supportChart) s (m + tensorOrder P) Z

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def norm (f : SupportedField (F := ComplexTensor) (modeSupport K)) (m : ℕ) : ℝ :=
  supportedWeightedSeminorm (chartSupport c.e (modeSupport K) c.supportChart) s m
    (tensorChartPush c.e c.smoothInverse (modeSupport K) c.supportChart f)

def κ (m : ℕ) : ℝ := max (SmallModes.errorConstant m (c.C m))
  (c.D m * SmallModes.initialConstant 4 (m + tensorOrder P) (c.C (m + tensorOrder P)))

def size (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (2 ^ m * (SmallModes.forcedModeBudget 4 (tensorOrder P) c.C c.D q m *
    c.norm f (m + (q + 1) * (tensorOrder P + 1)))) * c.J m ^ m

def residual (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q m : ℕ) : ℝ :=
  tensorChartBudget m (c.J m) (c.J (m + 1)) *
    (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ
        (fun r => c.κ r * c.norm f (r + (tensorOrder P + 1))) q m))

theorem exists_solution (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (c.size f q m) X) ∧
      (∀ m, WeightedBound Set.univ τ m (c.residual f q m)
        (fun x => coordinateFullLinearized P ε G X x + QuadraticMean.displacement τ (coordinatePhase φ) f x)) := by
  exact global_charted_forced_mode c.openO c.openU P c.smoothP hG c.mapsG K c.supportU
    c.smoothPhase τ ε c.e c.smoothForward c.smoothInverse c.supportChart c.phase c.smoothMap c.domain
    hτ hs hτs hs1 hε hsmall c.C c.D c.J c.nonnegC c.nonnegD c.oneLEJ c.coordinates c.coefficients c.polynomial f q

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
