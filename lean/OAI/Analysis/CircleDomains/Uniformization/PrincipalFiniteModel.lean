import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Modulus.PrincipalNormalization
import OAI.Analysis.CircleDomains.Uniformization.SmoothMetricUniformization

namespace OAI

/-!
# Principally normalized finite metric circle models

The spherical metric near infinity supplies an actual open neighborhood
where the metric model is holomorphic. The affine normalization there
preserves the circle domain, the smooth inverse, and the retained core.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem conformal_neighborhood_of_infty
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hinf : OnePoint.infty ∈ U)
    {g : (ℝ × ℝ) → PlanarMetric} (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    {R : ℝ} (hfar : ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) :
    ∃ W : Set Sphere, IsOpen W ∧ OnePoint.infty ∈ W ∧ W ⊆ U ∧ IsConformalOn f W := by
  let C : Set ℂ := Complex.equivRealProdCLM.symm '' Metric.closedBall 0 R
  have hC : IsCompact C := (isCompact_closedBall (0 : ℝ × ℝ) R).image Complex.equivRealProdCLM.symm.continuous
  let W : Set Sphere := U \ ((↑) : ℂ → Sphere) '' C
  have hW : IsOpen W := hU.sdiff (hC.image OnePoint.continuous_coe).isClosed
  have hi : OnePoint.infty ∈ W := by
    refine ⟨hinf, ?_⟩
    rintro ⟨z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  refine ⟨W, hW, hi, sdiff_subset, ?_⟩
  apply metric_conformal_on_spherical_background (fun p hp => hf p hp.1)
  intro z hz
  apply hfar
  intro hzball
  exact hz.2 ⟨z, ⟨Complex.equivRealProdCLM z, hzball,
    Complex.equivRealProdCLM.symm_apply_apply z⟩, rfl⟩

theorem smoothSphereEquivalence_affine (a b : ℂ) (ha : a ≠ 0) (U : Set Sphere) :
    IsSmoothSphereEquivalence (affineSphere a b ha) (affineSphere a b ha).symm U
      (affineSphere a b ha '' U) := by
  refine ⟨fun p _ => (show IsConformalOn (affineSphere a b ha) univ from
    fun q _ => isConformalAt_affineSphere a b ha q).isSmoothSphereAt isOpen_univ (mem_univ p),
    mapsTo_image _ _, fun p _ => ?_, ?_,
    fun p _ => (affineSphere a b ha).symm_apply_apply p,
    fun p _ => (affineSphere a b ha).apply_symm_apply p⟩
  · exact (show IsConformalOn (affineSphere a b ha).symm univ from
      fun q _ => isConformalAt_affineSphere_symm a b ha q).isSmoothSphereAt isOpen_univ (mem_univ p)
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [(affineSphere a b ha).symm_apply_apply] using hp

namespace FiniteTransfer

theorem principal_finite_metric_circle_model
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
      (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p) ∧ IsPrincipalNormalized f := by
  obtain ⟨V, f, fi, hV, heq, hc, hm, hfix⟩ :=
    smooth_finite_metric_circle_model_fixing_infty hcompact hfinite T hdisj hKQ g hg hPD hfar hcore
  obtain ⟨R, _, hR⟩ := hfar
  obtain ⟨W, hW, hiW, hWU, hfW⟩ := conformal_neighborhood_of_infty
    (isOpen_openCompletedRegion T) (hKQ (infty_mem_sphericalCore K)) hm hR
  obtain ⟨a, b, ha, hnorm⟩ := principal_normalize_at_infty hW hfW
    (heq.bijOn.injOn.mono hWU) hiW hfix
  let e := affineSphere a b ha
  refine ⟨e '' V, e ∘ f, fi ∘ e.symm,
    isCircleDomain_image_mobius hV (affineMobius a b ha) e (affineSphere_eq_smul a b ha),
    heq.trans (smoothSphereEquivalence_affine a b ha V), ?_, ?_, hnorm⟩
  · exact (show IsConformalOn e univ from fun p _ =>
      isConformalAt_affineSphere a b ha p).comp hc (mapsTo_univ _ _)
  · intro p hp
    exact (hm p hp).comp_conformal (isConformalAt_affineSphere a b ha _)

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
