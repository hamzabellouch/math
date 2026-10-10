import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseFamily
import OAI.Geometry.SurfaceImmersion.Atlas.UniformPhaseSolverPrefix
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! All charts and numeric profiles for nearby-map cancellation are fixed in advance. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem CompactPhaseFamily.uniform_solvers_all_profiles
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (R : ℕ → ℝ), (∀ m, 0 ≤ R m) →
    ∃ C J I : a.centers → ℕ → ℝ,
      (∀ i m, 0 ≤ C i m) ∧ (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ I i m) ∧
      (∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (a.charts i).chart.target,
        ‖iteratedFDerivWithin ℝ j (a.charts i).chart.symm (a.charts i).chart.target x‖ ≤ I i m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : (i : a.centers) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ
          (a.support i) τ s,
        (∀ i, (c i).e = (a.charts i).chart) ∧ (∀ i, (c i).C = C i) ∧
        (∀ i m, (c i).D m = 0) ∧ (∀ i, (c i).J = J i) := by
  classical
  choose ρ hρ hall using fun i =>
    (a.charts i).uniform_solvers_of_prefix_all_profiles hF hφ (a.support i) (a.support_chart i)
  obtain ⟨r,hr,_,hrρ⟩ := finite_positive_threshold ρ hρ
  refine ⟨r,hr,?_⟩
  intro R hR
  choose C J hC hJ hsolve using fun i => hall i R hR
  choose I hI hi using fun (i : a.centers) m => compact_local_weighted_bound
    (a.charts i).chart.open_target isOpen_univ (a.charts i).targetCompact.isCompact
    (a.charts i).targetBound (subset_univ _) (a.charts i).smoothInverse.contDiffOn m
  refine ⟨C,J,I,hC,hJ,hI,?_,?_⟩
  · intro i m j _ hj x hx
    simpa only [one_pow,one_mul] using hi i m 1 zero_le_one le_rfl j hj x hx
  · intro G hG B hB hBr hb τ s hs hs1 hp
    choose c he hc hd hj using fun i => hsolve i G hG B hB (hBr.trans_le (hrρ i))
      hb τ s hs hs1 hp
    exact ⟨c,he,hc,hd,hj⟩

theorem CompactPhaseFamily.uniform_solvers
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)
    (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (ρ : ℝ) (C J I : a.centers → ℕ → ℝ), 0 < ρ ∧
      (∀ i m, 0 ≤ C i m) ∧ (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ I i m) ∧
      (∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (a.charts i).chart.target,
        ‖iteratedFDerivWithin ℝ j (a.charts i).chart.symm (a.charts i).chart.target x‖ ≤ I i m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : (i : a.centers) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ
          (a.support i) τ s,
        (∀ i, (c i).e = (a.charts i).chart) ∧ (∀ i, (c i).C = C i) ∧
        (∀ i m, (c i).D m = 0) ∧ (∀ i, (c i).J = J i) := by
  obtain ⟨ρ,hρ,hall⟩ := a.uniform_solvers_all_profiles hF hφ
  obtain ⟨C,J,I,hC,hJ,hI,hi,hsolve⟩ := hall R hR
  exact ⟨ρ,C,J,I,hρ,hC,hJ,hI,hi,hsolve⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
