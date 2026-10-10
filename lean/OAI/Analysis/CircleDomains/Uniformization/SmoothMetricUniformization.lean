import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereEquivalence
import OAI.Analysis.CircleDomains.Modulus.NormalizedMetricUniformization

namespace OAI

/-!
# Smooth finite metric circle models and their inverses

The smooth version of the same compact uniformization input records
that the uniformizing map is a diffeomorphism for the original smooth
structure. This is the smooth-isothermal-coordinate conclusion of
Jost, *Compact Riemann Surfaces*, third edition (2006), Theorem 3.11.1,
pp. 155--158, followed by Ahlfors, *Conformal Invariants* (1973),
Theorem 10-3, p. 142. Only a smooth metric on the sphere, standard near
infinity, is required. The weaker metric-only input follows immediately.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def SmoothCompactMetricSphereUniformization : Prop :=
  ∀ (g : (ℝ × ℝ) → PlanarMetric), ContDiff ℝ ∞ g → (∀ z, (g z).PosDef) →
    (∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) →
    ∃ e : Sphere ≃ₜ Sphere, (∀ p, IsMetricConformalAt g e p) ∧
      (∀ p, IsSmoothSphereAt e p) ∧ (∀ p, IsSmoothSphereAt e.symm p)

theorem SmoothCompactMetricSphereUniformization.toMetric
    (h : SmoothCompactMetricSphereUniformization) : CompactMetricSphereUniformization := by
  intro g hg hpd hfar
  obtain ⟨e, he, _, _⟩ := h g hg hpd hfar
  exact ⟨e, he⟩

namespace FiniteTransfer

theorem smooth_finite_metric_circle_model
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) := by
  obtain ⟨e, he, hes, heis⟩ := hcompact g hg hPD hfar
  have hecore : IsConformalOn e (sphericalCore K) := by
    apply metric_conformal_on_spherical_background (fun p _ => he p)
    intro z hz
    exact hcore.self_of_nhdsSet _ ((coe_mem_sphericalCore K z).mp hz)
  obtain ⟨V, f, hV, _, hfcore, hfconf⟩ :=
    uniformize_finite_completion_of_jordan_models hfinite T hdisj e hKQ hecore
  obtain ⟨ki, hki⟩ := hfconf.exists_smooth_inverse
    (e.isOpenMap _ (isOpen_openCompletedRegion T)) hV.1
  have hequiv : IsSmoothSphereEquivalence e e.symm (openCompletedRegion T)
      (e '' openCompletedRegion T) := by
    refine ⟨fun p _ => hes p, mapsTo_image _ _, fun p _ => heis p, ?_,
      fun p _ => e.symm_apply_apply p, fun p _ => e.apply_symm_apply p⟩
    rintro _ ⟨p, hp, rfl⟩
    simpa only [e.symm_apply_apply] using hp
  have heq : (f ∘ e.symm) ∘ e = f := by
    funext p
    simp only [Function.comp_apply, e.symm_apply_apply]
  refine ⟨V, f, e.symm ∘ ki, hV, ?_, hfcore, ?_⟩
  · simpa only [heq] using hequiv.trans hki
  · intro p hp
    simpa only [heq] using (he p).comp_conformal (hfconf.1 _ ⟨p, hp, rfl⟩)

theorem smooth_finite_metric_circle_model_fixing_infty
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {K : Set (ℝ × ℝ)} (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g) (hPD : ∀ z, (g z).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1)
    (hcore : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    ∃ (V : Set Sphere) (f fi : Sphere → Sphere), IsCircleDomain V ∧
      IsSmoothSphereEquivalence f fi (openCompletedRegion T) V ∧
      IsConformalOn f (sphericalCore K) ∧
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) ∧
      f OnePoint.infty = OnePoint.infty := by
  obtain ⟨V, f, fi, hV, hequiv, hfcore, hfmetric⟩ :=
    smooth_finite_metric_circle_model hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  let e := pointToInfinity (f OnePoint.infty)
  refine ⟨e '' V, e ∘ f, fi ∘ e.symm, pointToInfinity_preserves_circleDomain _ hV,
    hequiv.trans (smoothSphereEquivalence_pointToInfinity _ V), ?_, ?_, ?_⟩
  · exact (show IsConformalOn e univ from fun p _ =>
      isConformalAt_pointToInfinity _ p).comp hfcore (mapsTo_univ _ _)
  · intro p hp
    exact (hfmetric p hp).comp_conformal (isConformalAt_pointToInfinity _ _)
  · exact pointToInfinity_apply_self _

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
