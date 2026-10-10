import OAI.Geometry.SurfaceImmersion.Correction.PolynomialChartedMetricMean
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFiniteMeanFamily
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamily

namespace OAI

/-! Polynomial estimates for arbitrary finite families of the actual
charted metric means. The cardinality enters the geometric profile. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

theorem polynomial_charted_metric_mean_family (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {ι : Type*} [Fintype ι] {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {s : ℝ≥0}
      (c : ∀ i, PolynomialSolveData P 0 G hG (φ i) (K i) τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) → (∀ m, (Fintype.card ι : ℝ) ≤ J m) →
      (∀ i m, ρ⁻¹ ≤ J m ∧ (d i).budgets.inv (m+q+2) ≤ J m ∧
        (d i).budgets.forms (m+q+2) ≤ J m ∧ (d i).budgets.psi (m+q+2) ≤ J m ∧
        (d i).budgets.mode (m+q+2) ≤ J m ∧ (d i).budgets.normal (m+q+2) ≤ J m ∧
        (d i).budgets.chi m ≤ J m ∧ (d i).budgets.pull m ≤ J m) →
      ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s reference r (q+2)
        (rescaledMean (τ/s) (chartedFamilyMean d hρ δ q))
        (polynomialMeanProfile p C J) (polynomialMeanProfile p C J) := by
  classical
  obtain ⟨p,C,hC,hm⟩ := polynomial_charted_metric_mean q
  refine ⟨fun m => p m+1,fun m => 1+C m,fun m => by linarith [hC m],?_⟩
  intro ι _ n P τ G hG φ K s c r ρ R reference d hρ hτ hs hτs hs1 J hJ hcard hb δ hδ
  have hlocal (i : ι) := hm (c i) (d i) hρ hτ hs hτs hs1 J hJ (hb i) δ hδ
  have hfamily := polynomial_finite_mean_family uniqueDiffOn_univ hs.le
    (reference := reference) (r := r) (L := q+2) (Finset.univ : Finset ι)
    (fun i => rescaledMean (τ/s) ((d i).mean hρ δ q)) p C J
    (fun m => zero_le_one.trans (hC m)) hJ (by simpa using hcard)
    (fun i _ => hlocal i)
  have he : rescaledMean (τ/s) (chartedFamilyMean d hρ δ q) =
      (fun θ f x => ∑ i ∈ (Finset.univ : Finset ι),
        rescaledMean (τ/s) ((d i).mean hρ δ q) θ f x) := by
    funext θ f x k
    simp [rescaledMean, chartedFamilyMean, Finset.mul_sum]
  rw [he]
  exact hfamily

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
