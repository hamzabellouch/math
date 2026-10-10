import OAI.Analysis.CircleDomains.Modulus.ConformalNormalization
import OAI.Analysis.CircleDomains.Uniformization.MetricUniformization

namespace OAI

/-!
# Finite circle models fixing infinity

Postcomposing the actual finite metric model by the explicit Möbius
normalizer retains all conformality conclusions. Injectivity then
ensures that every finite source point has a finite target coordinate.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem finite_image_of_fixes_infty
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hU : OnePoint.infty ∈ U) (hf : f OnePoint.infty = OnePoint.infty)
    {z : ℂ} (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty := by
  intro h
  exact OnePoint.coe_ne_infty z (hinj hz hU (h.trans hf.symm))

theorem normalize_metric_circle_model
    {U V K : Set Sphere} {f : Sphere → Sphere} {g : (ℝ × ℝ) → PlanarMetric}
    (hU : OnePoint.infty ∈ U) (hV : IsCircleDomain V) (hbij : BijOn f U V)
    (hcore : IsConformalOn f K) (hmetric : ∀ p ∈ U, IsMetricConformalAt g f p) :
    ∃ (W : Set Sphere) (ψ : Sphere → Sphere),
      IsCircleDomain W ∧ BijOn ψ U W ∧ IsConformalOn ψ K ∧
      (∀ p ∈ U, IsMetricConformalAt g ψ p) ∧ ψ OnePoint.infty = OnePoint.infty ∧
      (∀ z : ℂ, (z : Sphere) ∈ U → ψ (z : Sphere) ≠ OnePoint.infty) := by
  let e := pointToInfinity (f OnePoint.infty)
  let ψ : Sphere → Sphere := e ∘ f
  have hψbij : BijOn ψ U (e '' V) := e.injective.bijOn_image.comp hbij
  have hψinf : ψ OnePoint.infty = OnePoint.infty := pointToInfinity_apply_self _
  refine ⟨e '' V, ψ, pointToInfinity_preserves_circleDomain _ hV, hψbij, ?_, ?_, hψinf, ?_⟩
  · exact (show IsConformalOn e univ from fun p _ =>
      isConformalAt_pointToInfinity _ p).comp hcore (mapsTo_univ _ _)
  · intro p hp
    exact (hmetric p hp).comp_conformal (isConformalAt_pointToInfinity _ _)
  · intro z hz
    exact finite_image_of_fixes_infty hψbij.injOn hU hψinf hz

namespace FiniteTransfer

theorem uniformize_finite_metric_completion_fixing_infty
    (hcompact : CompactMetricSphereUniformization) (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) ∧
      f OnePoint.infty = OnePoint.infty ∧
      (∀ z : ℂ, (z : Sphere) ∈ openCompletedRegion T → f (z : Sphere) ≠ OnePoint.infty) := by
  obtain ⟨_, V, f, _, hV, hbij, hfcore, _, hfmetric⟩ :=
    uniformize_finite_metric_completion hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  exact normalize_metric_circle_model (hKQ (infty_mem_sphericalCore K)) hV hbij hfcore hfmetric

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
