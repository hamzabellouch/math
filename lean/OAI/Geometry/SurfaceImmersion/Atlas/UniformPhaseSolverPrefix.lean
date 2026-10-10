import OAI.Geometry.SurfaceImmersion.Atlas.UniformPhaseChartSolver
import OAI.Geometry.SurfaceImmersion.Geometry.RealJetPrefixBounds

namespace OAI

/-! Construct the scale-dependent solver from shifted bounds on the actual map. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates RealModes

theorem GoodPhaseChart.uniform_solvers_of_prefix_all_profiles
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ))
    (K : Compacts JetPolynomial.Base)
    (hK : (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (R : ℕ → ℝ), (∀ m, 0 ≤ R m) →
    ∃ C J : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 1 ≤ J m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e.chart ∧ c.C = C ∧ (∀ m, c.D m = 0) ∧ c.J = J := by
  obtain ⟨ρ,hρ,hall⟩ := e.uniform_unperturbed_solvers_all_profiles hF hφ K hK
  refine ⟨ρ,hρ,?_⟩
  intro R hR
  choose D hD hd using fun m => compact_realTwoJet_comp_prefix_bound e.smoothInverse
    e.targetCompact e.chart.open_target e.targetBound m
  let A := fun m => 1+D m*R m
  have hA (m : ℕ) : 1 ≤ A m :=
    le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hD m)) (hR m))
  obtain ⟨C,J,hC,hJ,hsolve⟩ := hall A hA
  refine ⟨C,J,hC,hJ,?_⟩
  intro G hG B hB hBρ hb τ s hs hs1 hp
  apply hsolve G hG B hB hBρ hb τ s hs hs1
  intro m
  apply (hd (m+1) (G ∘ planeCoordinateIsometry.symm)
    (hG.comp planeCoordinateIsometry.symm.contDiff) s (R (m+1)) hs hs1 (hR _)
    (hp (m+1))).mono_const
  exact le_add_of_nonneg_left zero_le_one

theorem GoodPhaseChart.uniform_solvers_of_prefix
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ))
    (K : Compacts JetPolynomial.Base)
    (hK : (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source)
    (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (ρ : ℝ) (C J : ℕ → ℝ), 0 < ρ ∧ (∀ m, 0 ≤ C m) ∧ (∀ m, 1 ≤ J m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e.chart ∧ c.C = C ∧ (∀ m, c.D m = 0) ∧ c.J = J := by
  obtain ⟨ρ,hρ,hall⟩ := e.uniform_solvers_of_prefix_all_profiles hF hφ K hK
  obtain ⟨C,J,hC,hJ,hsolve⟩ := hall R hR
  exact ⟨ρ,C,J,hρ,hC,hJ,hsolve⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
