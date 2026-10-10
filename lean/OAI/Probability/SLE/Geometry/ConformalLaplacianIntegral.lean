import OAI.Probability.SLE.Geometry.ExteriorLaplacianTest
import OAI.Probability.SLE.Gauge.ConformalSausageTransfer

namespace OAI

/-! Change of variables for the Laplacian of a smooth real test under
an injective holomorphic map. -/
noncomputable section
open Set Filter Metric Function MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma integral_laplacian_holomorphic_image {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) :
    (∫ z in f '' D, (Δ u) z)=(∫ z in D, (Δ (u ∘ f)) z) := by
  have hd (z : ℂ) (hz : z∈D) : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (hD.mem_nhds hz)).hasDerivAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hD.measurableSet
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hi]
  apply setIntegral_congr_fun hD.measurableSet
  intro z hz
  dsimp only
  rw [complex_derivative_real_det,abs_of_nonneg (sq_nonneg _),smul_eq_mul]
  exact (laplacian_holomorphic_comp (hf.analyticAt (hD.mem_nhds hz)) hu.contDiffAt).symm

lemma integrableOn_laplacian_holomorphic_comp {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) :
    IntegrableOn (Δ (u ∘ f)) D := by
  have hd (z : ℂ) (hz : z∈D) : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have hc : Continuous (Δ u) :=
    continuous_iff_continuousAt.mpr (fun z => plane_laplacian_continuousAt (hu.contDiffAt (x := z)))
  have hsu := hasCompactSupport_laplacian hs
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD.measurableSet
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hi (Δ u)).mp
      ((hc.integrable_of_hasCompactSupport hsu).integrableOn)
  apply hint.congr_fun _ hD.measurableSet
  intro z hz
  dsimp only
  rw [complex_derivative_real_det,abs_of_nonneg (sq_nonneg _),smul_eq_mul]
  exact (laplacian_holomorphic_comp (hf.analyticAt (hD.mem_nhds hz)) hu.contDiffAt).symm

lemma exterior_compact_test_laplacian_nonpos {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    (hK : IsCompact (f '' D)ᶜ) :
    ∃ u : ℂ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      (∀ z∈(f '' D)ᶜ, u =ᶠ[𝓝 z] (fun w => ‖w‖^2)) ∧
      IntegrableOn (Δ (u ∘ f)) D ∧ (∫ z in D, (Δ (u ∘ f)) z)≤0 := by
  obtain ⟨u,hu,hs,he,hn⟩ := compact_quadratic_test_complement_integral _ hK
  refine ⟨u,hu,hs,he,integrableOn_laplacian_holomorphic_comp hD hf hi hu hs,?_⟩
  rw [←integral_laplacian_holomorphic_image hD hf hi hu]
  simpa only [compl_compl] using hn

end SLEExactGauge

end

end OAI
