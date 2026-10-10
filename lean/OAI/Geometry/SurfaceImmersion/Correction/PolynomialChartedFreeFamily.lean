import OAI.Geometry.SurfaceImmersion.Correction.PolynomialChartedFree
import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeFamily

namespace OAI

/-! Polynomial free estimates uniform over the number of phase cells. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem polynomial_charted_free_family (q m : ℕ) :
    ∃ p : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {ι : Type*} [Fintype ι] {τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData emptyMetricPolynomial 0 G hG (φ i) (K i) τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ C J : ℕ → ℝ, (∀ i, (c i).C = C ∧ (c i).J = J ∧ ∀ j, (c i).D j = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      (∀ i, (d i).budgets.inv (m+q+1) ≤ B ∧ (d i).budgets.forms (m+q+1) ≤ B ∧
        (d i).budgets.psi (m+q+1) ≤ B) →
      ∀ N : ℕ → ℝ, (∀ j, 0 ≤ N j) →
      (∀ i, (d i).budgets.normal (m+q+1) ≤ N (m+q+1)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ f : SmallModes.Base → Tensor,
      ContDiff ℝ ∞ f → InTrialBall univ reference r f →
      WeightedBound univ s (m+q+1) B f →
      WeightedBound univ τ m
        ((Fintype.card ι : ℝ)*metricFreeSizeBudget C J N q m*(A*B^p)*(δ*τ))
        (chartedFreeSum d hρ δ q f) ∧
      WeightedBound univ τ m
        ((Fintype.card ι : ℝ)*(τ/s)^(q+1)*metricFreeResidualBudget C J N q m*(A*B^p)*(δ*τ))
        (coordinateFullLinearized emptyMetricPolynomial 0 G (chartedFreeSum d hρ δ q f)) := by
  classical
  obtain ⟨p,A,hA,hfree⟩ := polynomial_charted_free_bounds q m
  refine ⟨p,A,hA,?_⟩
  intro ι _ τ G hG φ K s c r ρ R reference d C J hc hρ hτ hs hτs hs1 B hB hρB hb N hN hn δ hδ f hfs hfb hbf
  have hi (i : ι) := hfree (d i) (hc i).2.2 hρ hτ hs hτs hs1 B hB hρB
    (hb i).1 (hb i).2.1 (hb i).2.2 N hN (hn i) δ hδ f hfs hfb hbf
  have hsize (i : ι) : WeightedBound univ τ m
      (metricFreeSizeBudget C J N q m*(A*B^p)*(δ*τ)) ((d i).displacement hρ δ q f) := by
    simpa only [(hc i).1,(hc i).2.1] using (hi i).1
  have hres (i : ι) : WeightedBound univ τ m
      ((τ/s)^(q+1)*metricFreeResidualBudget C J N q m*(A*B^p)*(δ*τ))
      (coordinateFullLinearized emptyMetricPolynomial 0 G ((d i).displacement hρ δ q f)) := by
    simpa only [(hc i).1,(hc i).2.1] using (hi i).2
  rw [chartedFreeSum_eq]
  constructor
  · have hh := WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun _ : ι => metricFreeSizeBudget C J N q m*(A*B^p)*(δ*τ))
      (fun i => (d i).displacement hρ δ q f)
      (fun i _ => ((d i).displacement_smooth_support hρ δ q f).1.contDiffOn)
      (fun i _ => hsize i)
    convert hh using 1
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  · rw [coordinateFullLinearized_sum emptyMetricPolynomial 0 G Finset.univ _
      (fun i => ((d i).displacement_smooth_support hρ δ q f).1)]
    have hh := WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun _ : ι => (τ/s)^(q+1)*metricFreeResidualBudget C J N q m*(A*B^p)*(δ*τ))
      (fun i => coordinateFullLinearized emptyMetricPolynomial 0 G ((d i).displacement hρ δ q f))
      (fun i _ => (coordinateFullLinearized_smooth (c i).openO (c i).openU emptyMetricPolynomial
        (c i).smoothP hG (c i).mapsG (K i) (c i).supportU
        ((d i).displacement_smooth_support hρ δ q f).1
        ((d i).displacement_smooth_support hρ δ q f).2 0).contDiffOn)
      (fun i _ => hres i)
    convert hh using 1
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
