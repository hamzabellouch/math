import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedGeometricSolver

namespace OAI

/-! Construct the actual metric solver with specified numerical bounds.
No compactness choice of coefficients is used by this constructor. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes

noncomputable def unperturbedSolverOfBounds
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (hdom : RealModeDomain ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) e.target)
    (τ : ℝ) (s : ℝ≥0) (C J : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 1 ≤ J m)
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound
      (fun p => complexify (G (planeCoordinateIsometry.symm (e.symm p)))) e.target s (m+1) (C m))
    (hj : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m) :
    PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s where
  U := univ
  O := univ
  openU := isOpen_univ
  openO := isOpen_univ
  smoothP := fun _ l => Fin.elim0 l
  mapsG := mapsTo_univ _ _
  supportU := subset_univ _
  smoothPhase := hφ
  e := e
  smoothForward := he.contDiffOn
  smoothInverse := hi.contDiffOn
  supportChart := hKe
  phase := hphase
  smoothMap := (hG.comp planeCoordinateIsometry.symm.contDiff).comp hi
  domain := hdom.complexDomain ((hG.comp planeCoordinateIsometry.symm.contDiff).comp hi)
  C := C
  D := fun _ => 0
  J := J
  nonnegC := hC
  nonnegD := fun _ => le_rfl
  oneLEJ := hJ
  coordinates := hj
  coefficients := hc
  polynomial := by
    intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
