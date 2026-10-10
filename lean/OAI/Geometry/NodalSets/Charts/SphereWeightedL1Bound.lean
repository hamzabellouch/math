import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Map

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereWeightedL1BoundMeasurable : MeasurableSpace Base := borel Base
local instance sphereWeightedL1BoundBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_reference_L1_bound (d : SphereEnergyData) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ u : SphereEnergySmooth d,
      (∫ x, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ∂sphereReferenceMeasure) ≤
        B*‖sphereEnergyL2Linear d u‖ := by
  have hi : Continuous (fun x ↦ (d.density x)⁻¹) := d.continuous.inv₀ (fun x ↦ (d.positive x).ne')
  let g := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) _ hi
  refine ⟨‖g‖,norm_nonneg _,?_⟩
  intro u
  let f : Base → ℝ := fun x ↦ |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x|
  have hf : Continuous f := (SphereEnergySmooth.toSmooth d u).property.continuous.abs
  let L := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) f hf
  have hn : ‖L‖ = ‖sphereEnergyL2Linear d u‖ := by
    have hL := sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le) f hf
    have hu := sphereEnergyL2Linear_norm_sq d u
    have he : sphereWeightedPairing d.density f f =
        sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        dsimp [f]
        simp only [mul_assoc,← sq,sq_abs])
    rw [he] at hL
    change ‖L‖^2 = _ at hL
    nlinarith [norm_nonneg L,norm_nonneg (sphereEnergyL2Linear d u)]
  have he : inner ℝ L g = ∫ x, f x ∂sphereReferenceMeasure := by
    rw [sphereWeightedToLp_inner]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      change d.density x*f x*(d.density x)⁻¹ = f x
      field_simp [(d.positive x).ne'])
  have h := real_inner_le_norm L g
  rw [he,hn] at h
  exact h.trans_eq (mul_comm _ _)

end
end Yau.Target

end OAI
