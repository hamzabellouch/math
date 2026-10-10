import OAI.MeasureTheory.Falconer.Estimates.RotatedLaws

namespace OAI

/-! # Rotation of the original measurable tube relation and its finite labels -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι : Type*}

noncomputable def rotatedTubeRelation (e : Space d ≃ₗᵢ[ℝ] Space d)
    (E : Set (Space d × Sphere d)) : Set (Space d × Sphere d) :=
  (Prod.map e.symm (sphereMap e.symm)) ⁻¹' E

theorem rotatedTubeRelation_measurable (e : Space d ≃ₗᵢ[ℝ] Space d)
    {E : Set (Space d × Sphere d)} (hE : MeasurableSet E) :
    MeasurableSet (rotatedTubeRelation e E) :=
  hE.preimage (e.symm.continuous.measurable.prodMap (continuous_sphereMap e.symm).measurable)

theorem rotatedTubeRelation_point_bound (e : Space d ≃ₗᵢ[ℝ] Space d)
    {E : Set (Space d × Sphere d)} {D : ℝ} (hE : ∀ u ∈ E, ‖u.1‖ ≤ D) :
    ∀ u ∈ rotatedTubeRelation e E, ‖u.1‖ ≤ D := by
  intro u hu
  have hh := hE _ hu
  change ‖e.symm u.1‖ ≤ D at hh
  simpa only [e.symm.norm_map] using hh

theorem rotatedTubeRelation_cover [DecidableEq ι]
    (e : Space d ≃ₗᵢ[ℝ] Space d) {E : Set (Space d × Sphere d)}
    (J : Sphere d → Finset ι) (v : ι → Space d) {r : ℝ}
    (hE : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-v i)‖ ≤ r) :
    ∀ u ∈ rotatedTubeRelation e E, ∃ i ∈ J (sphereMap e.symm u.2),
      ‖perpendicularPart (u.2:Space d) (u.1-e (v i))‖ ≤ r := by
  intro u hu
  obtain ⟨i,hi,hp⟩ := hE _ hu
  refine ⟨i,hi,?_⟩
  have he := rotated_perpendicular_norm e (e.symm (u.2:Space d)) (e.symm u.1) (v i)
  rw [e.apply_symm_apply,e.apply_symm_apply] at he
  rw [he]
  exact hp

theorem rotated_point_norm_ae (μ : Measure (Space d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    ∀ᵐ x ∂Measure.map e μ, ‖x‖ ≤ D := by
  rw [ae_map_iff e.continuous.measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  simpa only [e.norm_map] using hμ

theorem rotated_direction_cap_ae (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) {w₀ : Sphere d} {ρ : ℝ}
    (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ) :
    ∀ᵐ w ∂Measure.map (sphereMap e) ν, dist w (sphereMap e w₀) ≤ ρ := by
  rw [ae_map_iff (continuous_sphereMap e).measurable.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  simpa only [sphereMap_distance] using hν

end Falconer

end OAI
