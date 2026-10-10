import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones

namespace OAI

/-! # Pulling back distinct positive rays through a surjective height map -/

noncomputable section
namespace PolycyclicRecognition

/-- If a target ray pulls back to a positive multiple of a source generator
weight, every other target ray has a quotient that kills that generator. -/
theorem outside_ray_of_surjective_pullback
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (θ : V →ₗ[ℝ] W) (hθ : Function.Surjective θ)
    (α γ : W →ₗ[ℝ] ℝ) (β : V →ₗ[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (hmatch : α.comp θ = t • β)
    (hout : γ ∉ positiveWeightRay α) : β ∉ positiveWeightRay (γ.comp θ) := by
  rintro ⟨s, hs, hβ⟩
  have hαγ : α = (t * s) • γ := by
    ext w
    obtain ⟨v, rfl⟩ := hθ w
    have hh := LinearMap.congr_fun hmatch v
    rw [hβ] at hh
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, mul_assoc] using hh
  have hts : t * s ≠ 0 := (mul_pos ht hs).ne'
  apply hout
  refine ⟨(t * s)⁻¹, inv_pos.mpr (mul_pos ht hs), ?_⟩
  rw [hαγ, smul_smul, inv_mul_cancel₀ hts, one_smul]

end PolycyclicRecognition

end

end OAI
