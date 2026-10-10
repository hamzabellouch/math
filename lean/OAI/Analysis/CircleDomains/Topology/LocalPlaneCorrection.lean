import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity
import OAI.Analysis.CircleDomains.Topology.QuotientLocalChart
import OAI.Analysis.CircleDomains.Sobolev.DustSmoothingTolerance

namespace OAI

/-! A physical smoothing error on a finite quotient chart descends to a
bounded correction. Its dust-distance tolerance forces it to vanish at
every dust point, including along approaches from other charts. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem exists_local_plane_correction
    {G U S : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hS : IsOpen S)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, (e y).val = π y.val) (hinf : π OnePoint.infty ∉ S)
    (δ : ℝ) (hδ : δ ∈ Icc 0 1) (r : EuclideanPlane → ℝ)
    (hr : ContinuousOn r (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))
    (hbound : ∀ p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S),
      |r p| ≤ dustSmoothingTolerance (π ∘ planeSphere) Uᶜ δ p) :
    ∃ R : Sphere → ℝ,
      ContinuousOn R (U ∩ S) ∧
      (∀ p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S), R (π (planeSphere p)) = r p) ∧
      (∀ x, |R x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      (∀ x, |R x| ≤ 1) ∧
      ∀ x ∈ Uᶜ, Tendsto R (𝓝 x) (𝓝 0) := by
  classical
  let R : Sphere → ℝ := fun x => if hx : x ∈ U ∩ S then
    sphereFromPlaneFunction r (e.symm ⟨x, hx.1⟩).val else 0
  have hmap (p : G) : π p.val = (e p).val := (he p).symm
  have hRmap (p : Sphere) (hp : p ∈ G) (hS' : π p ∈ S) :
      R (π p) = sphereFromPlaneFunction r p := by
    have hx : π p ∈ U ∩ S := ⟨(hmap ⟨p, hp⟩) ▸ (e ⟨p, hp⟩).property, hS'⟩
    have heq : (⟨π p, hx.1⟩ : U) = e ⟨p, hp⟩ := Subtype.ext (hmap ⟨p, hp⟩)
    simp only [R, dite_eq_left hx, heq, Homeomorph.symm_apply_apply]
  have hplane (p : EuclideanPlane) (hp : p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S)) :
      R (π (planeSphere p)) = r p := by
    rw [hRmap (planeSphere p) hp.1 hp.2]
    change sphereFromPlaneFunction r (complexPlaneCoordinates p : Sphere) = r p
    rw [sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hphysical : ContinuousOn (sphereFromPlaneFunction r) (G ∩ π ⁻¹' S) := by
    intro y hy
    cases y using OnePoint.rec with
    | infty => exact (hinf hy.2).elim
    | coe z =>
      have hz : complexPlaneCoordinates.symm z ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S) := by
        change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G ∩ π ⁻¹' S
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
      have hopen := (hG.inter (hS.preimage hπ)).preimage continuous_planeSphere
      exact (sphereFromPlaneFunction_continuousAt_coe
        (hr.continuousAt (hopen.mem_nhds hz))).continuousWithinAt
  have hRcont : ContinuousOn R (U ∩ S) := by
    let q : ↥(U ∩ S) → G := fun x => e.symm ⟨x.val, x.property.1⟩
    have hq : Continuous q := e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun x => x.property.1)
    have hqs (x : ↥(U ∩ S)) : π (q x).val ∈ S := by
      have hx : π (q x).val = x.val := (he (q x)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply ⟨x.val, x.property.1⟩))
      rw [hx]
      exact x.property.2
    have hc := hphysical.comp_continuous (continuous_subtype_val.comp hq)
      (fun x => ⟨(q x).property, hqs x⟩)
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hc using 1
    funext x
    exact dite_eq_left x.property
  have hb (x : Sphere) : |R x| ≤ dustSmoothingTolerance id Uᶜ δ x := by
    by_cases hx : x ∈ U ∩ S
    · obtain ⟨z, hz, hez⟩ := quotient_neighborhood_chart_covers e π he hinf x hx
      let p := complexPlaneCoordinates.symm z
      have hp : p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S) := by
        change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G ∩ π ⁻¹' S
        simpa only [ContinuousLinearEquiv.apply_symm_apply, mem_preimage, mem_inter_iff] using hz
      have hpq : π (planeSphere p) = x := by
        simpa only [p, planeSphere, ContinuousLinearEquiv.apply_symm_apply] using hez
      rw [← hpq, hplane p hp]
      exact hbound p hp
    · simp only [R, dite_eq_right hx, abs_zero]
      exact div_nonneg (le_min hδ.1 infDist_nonneg) (by norm_num)
  refine ⟨R, hRcont, hplane, hb, ?_, ?_⟩
  · intro x
    exact (hb x).trans ((dustSmoothingTolerance_le_half id Uᶜ δ x).trans (by linarith [hδ.2]))
  · intro x hx
    exact tendsto_zero_of_abs_le_tolerance
      (dustSmoothingTolerance_tendsto_zero id Uᶜ hx hδ.1 tendsto_id)
      (Eventually.of_forall hb)

end CircleDomainRigidity

end

end OAI
