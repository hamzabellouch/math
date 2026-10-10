import OAI.MathematicalPhysics.Boltzmann.Branching.NormalReflectionGeometry

namespace OAI

/-! # Orthogonal changes of coordinates preserve the actual sphere area measure -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness

def sphereIsometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) : Sphere ≃ᵐ Sphere where
  toFun n := ⟨R n.1,by simpa only [Metric.mem_sphere,dist_zero_right,R.norm_map] using n.property⟩
  invFun n := ⟨R.symm n.1,by simpa only [Metric.mem_sphere,dist_zero_right,R.symm.norm_map] using n.property⟩
  left_inv n := by apply Subtype.ext; exact R.symm_apply_apply _
  right_inv n := by apply Subtype.ext; exact R.apply_symm_apply _
  measurable_toFun := by
    exact (R.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    exact (R.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

theorem sphereIsometry_cone (R : Velocity ≃ₗᵢ[ℝ] Velocity) (S : Set Sphere) :
    (Ioo (0:ℝ) 1) • ((↑) '' ((sphereIsometry R) ⁻¹' S)) =
      R ⁻¹' ((Ioo (0:ℝ) 1) • ((↑) '' S)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨n,hn,hny⟩,hxy⟩
    subst y
    change R x ∈ (Ioo (0:ℝ) 1) • ((↑) '' S)
    refine ⟨r,hr,R n.1,⟨sphereIsometry R n,hn,rfl⟩,?_⟩
    change r • R n.1 = R x
    change r • n.1 = x at hxy
    rw [← R.map_smul,hxy]
  · rintro ⟨r,hr,y,⟨n,hn,hny⟩,hxy⟩
    subst y
    refine ⟨r,hr,R.symm n.1,⟨(sphereIsometry R).symm n,?_,rfl⟩,?_⟩
    · change sphereIsometry R ((sphereIsometry R).symm n) ∈ S
      simpa only [MeasurableEquiv.apply_symm_apply] using hn
    · apply R.injective
      rw [R.map_smul,R.apply_symm_apply]
      exact hxy

theorem sphereIsometry_measurePreserving (R : Velocity ≃ₗᵢ[ℝ] Velocity) :
    MeasurePreserving (sphereIsometry R) sphereArea sphereArea := by
  refine ⟨(sphereIsometry R).measurable,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (sphereIsometry R).measurable hS,sphereArea,
    Measure.toSphere_apply' _ ((sphereIsometry R).measurable hS),Measure.toSphere_apply' _ hS,
    sphereIsometry_cone]
  congr 1
  change volume (R.toHomeomorph ⁻¹' _) = volume _
  rw [← R.toHomeomorph.measurableEmbedding.map_apply]
  change (volume.map R) _ = volume _
  rw [R.measurePreserving.map_eq]

end BoltzmannNonuniqueness

end

end OAI
