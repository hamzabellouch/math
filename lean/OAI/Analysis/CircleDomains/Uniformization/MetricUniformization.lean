import OAI.Analysis.CircleDomains.Sobolev.MetricComposition
import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletionUniformization
import OAI.Analysis.CircleDomains.Transfer.CoreGeometry

namespace OAI

/-!
# Conditional uniformization of a finite metric completion

`CompactMetricSphereUniformization` is the smooth metric-sphere
specialization of compact genus-zero uniformization: Ahlfors,
*Conformal Invariants* (1973), Theorem 10-3, p. 142, together with
the smooth isothermal-coordinate construction in Jost,
*Compact Riemann Surfaces*, third edition (2006), Theorem 3.11.1,
pp. 155--158.
The metric formulation is also stated at the start of Hedenmalm--Shimorin,
*Hele--Shaw flow on hyperbolic surfaces*, J. Math. Pures Appl. 81
(2002), pp. 187--188, equation (1.1). Its output records
metric conformality of the actual real differential in sphere charts,
including positive orientation. The metric agrees with the spherical
metric near infinity, so it defines a smooth metric on the sphere.

Together with Conway's finite circle theorem, this gives a circle model
for the actual terminal-disk completion that retains holomorphy on the
prescribed core. Both published inputs remain explicit parameters.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def CompactMetricSphereUniformization : Prop :=
  ∀ (g : (ℝ × ℝ) → PlanarMetric), ContDiff ℝ ∞ g → (∀ z, (g z).PosDef) →
    (∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) →
    ∃ e : Sphere ≃ₜ Sphere, ∀ p, IsMetricConformalAt g e p

namespace FiniteTransfer

theorem uniformize_finite_metric_completion
    (hcompact : CompactMetricSphereUniformization) (hfinite : FiniteCircleUniformization)
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
    uniformize_finite_completion_after_homeomorphism hfinite T hdisj e hKQ hecore
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
