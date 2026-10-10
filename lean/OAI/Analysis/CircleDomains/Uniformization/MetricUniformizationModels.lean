import OAI.Analysis.CircleDomains.Uniformization.MetricUniformization
import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput

namespace OAI

/-! Metric finite models using only the exact finite Jordan specialization. -/
open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteTransfer

theorem uniformize_finite_metric_completion_of_jordan_models
    (hcompact : CompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (e : Sphere ≃ₜ Sphere) (V : Set Sphere) (f : Sphere → Sphere),
      (∀ p, IsMetricConformalAt g e p) ∧ IsCircleDomain V ∧
      BijOn f (openCompletedRegion T) V ∧ IsConformalOn f (sphericalCore K) ∧
      IsConformalEquivalence (f ∘ e.symm) (e '' openCompletedRegion T) V ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) := by
  obtain ⟨e, he⟩ := hcompact g hg hPD hfar
  have hecore : IsConformalOn e (sphericalCore K) := by
    apply metric_conformal_on_spherical_background (fun p _ => he p)
    intro z hz
    have hzK : Complex.equivRealProdCLM z ∈ K := (coe_mem_sphericalCore K z).mp hz
    exact hcore.self_of_nhdsSet _ hzK
  obtain ⟨V, f, hV, hbij, hfcore, hfconf⟩ :=
    uniformize_finite_completion_of_jordan_models hfinite T hdisj e hKQ hecore
  refine ⟨e, V, f, he, hV, hbij, hfcore, hfconf, ?_⟩
  intro p hp
  have hcomp := (he p).comp_conformal (hfconf.1 (e p) ⟨p, hp, rfl⟩)
  have heq : (f ∘ e.symm) ∘ e = f := by
    funext x
    simp only [Function.comp_apply, e.symm_apply_apply]
  simpa only [heq] using hcomp


end FiniteTransfer
end CircleDomainRigidity

end

end OAI
