import OAI.Geometry.NodalSets.Charts.SphereEnergyBilinear
import OAI.Geometry.NodalSets.Charts.SphereSimplicitySquare
import OAI.Geometry.NodalSets.Elliptic.SimplicityCoordinateEnergy

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance sphereSimplicityEnergyLocal1 : MeasurableSpace Base := borel Base
local instance sphereSimplicityEnergyLocal2 : BorelSpace Base := ⟨rfl⟩

lemma roundCotangentTensor_seed_diagonal (v : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (x : Yau.Jets.Coord) :
    roundCotangentTensor (seedSphereFromCoord x)
      (sphereDifferential v (seedSphereFromCoord x)) (sphereDifferential v (seedSphereFromCoord x)) =
      Yau.pairing (v ∘ seedSphereFromCoord) (roundCoordGradient (v ∘ seedSphereFromCoord)) x := by
  have h := roundCotangentTensor_differential_pair v v hv hv seedPoint x
  change roundCotangentTensor (seedSphereFromCoord x)
    (sphereDifferential v (seedSphereFromCoord x)) (sphereDifferential v (seedSphereFromCoord x)) =
    roundCoordFactor x * ∑ i, Yau.coordPartial (v ∘ seedSphereFromCoord) x i *
    Yau.coordPartial (v ∘ seedSphereFromCoord) x i at h
  rw [h]
  unfold Yau.pairing roundCoordGradient Yau.coordPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sphere_simplicity_energy_eq_coordinate (u v a b : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (zeta : Yau.Jets.Coord → ℝ) (lam : ℝ)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) :
    sphereEnergyForm a b lam v v =
      roundSimplicityEnergy (u ∘ seedSphereFromCoord) (v ∘ seedSphereFromCoord) zeta lam := by
  rw [sphereEnergyForm,sphereReferenceMeasure_integral]
  unfold roundSimplicityEnergy
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change roundCoordDensity x*sphereEnergyDensity a b lam v v (seedSphereFromCoord x) = _
  rw [sphereEnergyDensity,roundTensorPerturbation_apply,roundCotangentTensor_seed_diagonal v hv,ha,hb]
  simp only [Function.comp_apply]
  ring

theorem sphere_simplicity_energy_identity (u v a b Z : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (lam : ℝ) (hlam : lam ≠ 0)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)
    (hZ : ∀ x, Z (seedSphereFromCoord x) = zeta x) :
    Integrable (sphereEnergyDensity a b lam v v) sphereReferenceMeasure ∧
    Integrable (fun p ↦ Z p*roundCotangentTensor p (sphereCrossDifferential u v p)
      (sphereCrossDifferential u v p)) sphereReferenceMeasure ∧
    sphereEnergyForm a b lam v v = ∫ p, Z p*roundCotangentTensor p
      (sphereCrossDifferential u v p) (sphereCrossDifferential u v p) ∂sphereReferenceMeasure := by
  have hu' : ContDiff ℝ ∞ (u ∘ seedSphereFromCoord) := spherePullback_smooth u hu seedPoint
  have hv' : ContDiff ℝ ∞ (v ∘ seedSphereFromCoord) := spherePullback_smooth v hv seedPoint
  obtain ⟨hi,he⟩ := round_simplicity_energy_identity _ _ zeta hu' hv' hz hc lam hlam
  have hsq (x : Yau.Jets.Coord) :
      roundCotangentTensor (seedSphereFromCoord x)
        (sphereCrossDifferential u v (seedSphereFromCoord x))
        (sphereCrossDifferential u v (seedSphereFromCoord x)) =
        roundSimplicitySquare (u ∘ seedSphereFromCoord) (v ∘ seedSphereFromCoord) x :=
    sphereCrossDifferential_square_chart u v hu hv seedPoint x
  refine ⟨?_,?_,?_⟩
  · rw [sphereReferenceMeasure_integrable]
    convert hi using 1
    funext x
    rw [sphereEnergyDensity,roundTensorPerturbation_apply,roundCotangentTensor_seed_diagonal v hv,ha,hb]
    simp only [Function.comp_apply]
    ring
  · rw [sphereReferenceMeasure_integrable]
    simp only [hsq,hZ,← mul_assoc]
    exact round_simplicity_square_integrable _ _ zeta hu' hv' hz hc
  · rw [sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb,he,
      sphereReferenceMeasure_integral]
    simp only [hsq,hZ,mul_assoc]

end
end Yau.Target

end OAI
