import OAI.Geometry.SurfaceImmersion.Atlas.UniformPhaseChartBounds
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedGeometricSolver

namespace OAI

/-! One fixed phase chart supplies solvers throughout a controlled C2 neighborhood. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates RealModes

/-- The chart, coordinate constants and reconstruction profile are chosen
before the nearby map, wavelength and slow scale. -/
theorem GoodPhaseChart.uniform_unperturbed_solvers_all_profiles
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ))
    (K : Compacts JetPolynomial.Base)
    (hK : (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (A : ℕ → ℝ), (∀ m, 1 ≤ A m) →
    ∃ C J : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 1 ≤ J m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, WeightedBound e.chart.target s (m+1) (A (m+1))
        (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘ e.chart.symm))) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e.chart ∧ c.C = C ∧ (∀ m, c.D m = 0) ∧ c.J = J := by
  obtain ⟨ρ,D,E,hρ,hD,_,hnear⟩ := e.uniform_mode_bounds (hF.comp planeCoordinateIsometry.symm.contDiff)
  refine ⟨ρ,hρ,?_⟩
  intro A hA
  choose J hJ hj using fun m => compact_local_weighted_bound e.chart.open_source isOpen_univ
    e.sourceCompact.isCompact e.sourceBound (subset_univ _) e.smooth.contDiffOn m
  let C := fun m => ((m+1).factorial : ℝ) * D (m+1) * A (m+1)^(m+1)
  have hC (m : ℕ) : 0 ≤ C m := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hD _)))
    (pow_nonneg (zero_le_one.trans (hA _)) _)
  refine ⟨C,J,hC,hJ,?_⟩
  intro G hG B hB hBρ hb τ s hs hs1 hjet
  have hGp := hG.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨hdom,hbounds⟩ := hnear (G ∘ planeCoordinateIsometry.symm) hGp B hB hBρ hb
  have hmap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.chart.symm) :=
    hGp.comp e.smoothInverse
  have hP : ∀ k l, (emptyMetricPolynomial k l).SmoothCoeffs univ := fun _ l => Fin.elim0 l
  refine ⟨{
    U := univ
    O := univ
    openU := isOpen_univ
    openO := isOpen_univ
    smoothP := hP
    mapsG := mapsTo_univ _ _
    supportU := subset_univ _
    smoothPhase := hφ
    e := e.chart
    smoothForward := e.smooth.contDiffOn
    smoothInverse := e.smoothInverse.contDiffOn
    supportChart := hK
    phase := fun x _ => e.phase x
    smoothMap := hmap
    domain := hdom.complexDomain hmap
    C := C
    D := fun _ => 0
    J := J
    nonnegC := hC
    nonnegD := fun _ => le_rfl
    oneLEJ := hJ
    coordinates := ?_
    coefficients := fun m => (hbounds (m+1) s (A (m+1)) hs (hA _) (hjet m)).1
    polynomial := ?_
  },rfl,rfl,fun _ => rfl,rfl⟩
  · intro m j _ hjm x hx
    simpa only [one_pow,one_mul] using hj m 1 zero_le_one le_rfl j hjm x hx
  · intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp

/-- The chart, coordinate constants and reconstruction profile are chosen
before the nearby map, wavelength and slow scale. -/
theorem GoodPhaseChart.uniform_unperturbed_solvers
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ))
    (K : Compacts JetPolynomial.Base)
    (hK : (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source)
    (A : ℕ → ℝ) (hA : ∀ m, 1 ≤ A m) :
    ∃ (ρ : ℝ) (C J : ℕ → ℝ), 0 < ρ ∧ (∀ m, 0 ≤ C m) ∧ (∀ m, 1 ≤ J m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, WeightedBound e.chart.target s (m+1) (A (m+1))
        (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘ e.chart.symm))) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e.chart ∧ c.C = C ∧ (∀ m, c.D m = 0) ∧ c.J = J := by
  obtain ⟨ρ,hρ,hall⟩ := e.uniform_unperturbed_solvers_all_profiles hF hφ K hK
  obtain ⟨C,J,hC,hJ,hsolve⟩ := hall A hA
  exact ⟨ρ,C,J,hρ,hC,hJ,hsolve⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
