import OAI.Geometry.SurfaceImmersion.Correction.UniformGeometricMeanData
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData

namespace OAI

/-! Build a uniformly profiled three-phase family from fixed geometric
unit-scale data, also allowing a smaller trial radius. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

theorem unit_mean_family_uniform {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Fin 3 → Base → ℝ}
    {K : Fin 3 → Compacts Base} (c₀ : ∀ j, PolynomialSolveData P 0 G hG (φ j) (K j) 1 1)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d₀ : ∀ j, ChartedMeanData (c₀ j) r ρ R reference) :
    ∃ p : Fin 3 → ChartedMeanProfile P, ∀ (ε τ : ℝ) (s : ℝ≥0) (r' : ℝ), r' ≤ r →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      ∃ d : ChartedMeanFamilyData P ε τ s r' ρ R reference,
        d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = K ∧
        (∀ j, (d.solver j).e = (c₀ j).e) ∧
        (∀ j x, (d.data j).cutoff x = (d₀ j).cutoff x) ∧
        (∀ j, (d.data j).form = (d₀ j).form) := by
  choose p hp using fun j => unit_mean_data_uniform_family (c₀ j) (d₀ j)
  refine ⟨p,?_⟩
  intro ε τ s r' hr hτ hs hτs hs1 hε hε1
  choose c d hfit he hcut hform using fun j => hp j ε τ s r' hr hτ hs hτs hs1 hε hε1
  refine ⟨{
    G := G
    smoothG := hG
    phase := φ
    support := K
    solver := c
    data := d
  },hfit,rfl,rfl,rfl,he,hcut,hform⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
