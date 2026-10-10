import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoareaCoordinates
import OAI.Analysis.CircleDomains.Sobolev.SobolevScalarCoarea
import OAI.Analysis.CircleDomains.Sobolev.CoareaInput

namespace OAI

/-! Exact transport of weighted scalar levels and differential energy
between the complex chart and the physical Euclidean plane. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma complex_weighted_level_eq_physical (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) (t : ℝ) :
    weightedScalarLevelLength (complexPlaneCoordinates '' E)
      (u ∘ complexPlaneCoordinates.symm) (q ∘ complexPlaneCoordinates.symm) t =
      sobolevLevelIntegral E u q t := by
  have hp : complexPlaneCoordinates ⁻¹'
      ((complexPlaneCoordinates '' E) ∩ {z | (u ∘ complexPlaneCoordinates.symm) z = t}) =
        E ∩ {x | u x = t} := by
    ext x
    simp only [mem_preimage,mem_inter_iff,mem_image,mem_ofPred_eq,comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    constructor
    · rintro ⟨⟨y,hy,hxy⟩,hx⟩
      have he : y = x := complexPlaneCoordinates.injective hxy
      exact ⟨he ▸ hy,hx⟩
    · rintro ⟨hx,hu⟩
      exact ⟨⟨x,hx,rfl⟩,hu⟩
  have h := (physical_complex_hausdorff_preserving 1).setLIntegral_comp_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding (q ∘ complexPlaneCoordinates.symm)
    ((complexPlaneCoordinates '' E) ∩ {z | (u ∘ complexPlaneCoordinates.symm) z = t})
  rw [hp] at h
  simpa only [weightedScalarLevelLength,sobolevLevelIntegral,comp_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h.symm

lemma complex_weighted_energy_eq_physical (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) :
    (∫⁻ z in complexPlaneCoordinates '' E, (q ∘ complexPlaneCoordinates.symm) z *
      ENNReal.ofReal ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖) =
      ∫⁻ x in E, q x * ENNReal.ofReal ‖fderiv ℝ u x‖ := by
  have h := complexPlaneCoordinates_measurePreserving.setLIntegral_comp_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding
    (fun z => (q ∘ complexPlaneCoordinates.symm) z * ENNReal.ofReal
      ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖) (complexPlaneCoordinates '' E)
  rw [Set.preimage_image_eq _ complexPlaneCoordinates.injective] at h
  simpa only [comp_apply,complex_precomposition_fderiv_norm,
    ContinuousLinearEquiv.symm_apply_apply] using h.symm

end CircleDomainRigidity

end

end OAI
