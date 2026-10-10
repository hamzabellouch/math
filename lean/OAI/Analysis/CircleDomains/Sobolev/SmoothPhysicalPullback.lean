import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorEnergy
import OAI.Analysis.CircleDomains.Sobolev.QuasiconformalSobolev
import OAI.Geometry.Cannon.Beltrami.DirichletPullback

namespace OAI

/-! Smooth quasiconformal pullback energy in the actual physical plane.
Only the finite compact-set estimate needed for the limiting scalar
transport is asserted. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def physicalSmoothEnergy (u : EuclideanPlane → ℝ) (x : EuclideanPlane) : ℝ :=
  (fderiv ℝ u x (EuclideanSpace.single 0 1))^2 +
    (fderiv ℝ u x (EuclideanSpace.single 1 1))^2

lemma physicalSmoothEnergy_eq_complex {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : EuclideanPlane) :
    physicalSmoothEnergy u x =
      ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)‖^2 := by
  rw [complexCovector_norm_sq, ← complexPlaneCoordinates_zero,
    ← complexPlaneCoordinates_one]
  simp only [Function.comp_def]
  rw [physical_complex_partial hu, physical_complex_partial hu]
  rfl

lemma physicalSmoothEnergy_integral {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (S : Set EuclideanPlane) :
    (∫ x in S, physicalSmoothEnergy u x) =
      ∫ z in complexPlaneCoordinates '' S,
        ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2 := by
  calc
    _ = ∫ x in S,
        ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)‖^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (physicalSmoothEnergy_eq_complex hu)
    _ = _ := by
      have h := complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
        complexPlaneCoordinates.toHomeomorph.measurableEmbedding
        (fun z => ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2)
        (complexPlaneCoordinates '' S)
      simpa only [preimage_image_eq _ complexPlaneCoordinates.injective] using h

lemma physicalHomeomorph_contDiff (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalHomeomorph F : EuclideanPlane → EuclideanPlane) :=
  complexPlaneCoordinates.symm.contDiff.comp (hF.comp complexPlaneCoordinates.contDiff)

lemma physicalSmoothPullback_energy (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ))
    {u : EuclideanPlane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤
      K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    {S : Set EuclideanPlane} (hS : IsCompact S) :
    (∫ x in S, physicalSmoothEnergy (u ∘ physicalHomeomorph F) x) ≤
      K*(∫ x in physicalHomeomorph F '' S, physicalSmoothEnergy u x) := by
  have hv := hu.comp (physicalHomeomorph_contDiff F hF)
  have he : (u ∘ physicalHomeomorph F) ∘ complexPlaneCoordinates.symm =
      (u ∘ complexPlaneCoordinates.symm) ∘ F := by
    funext z
    simp only [Function.comp_apply, physicalHomeomorph_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hi : F '' (complexPlaneCoordinates '' S) =
      complexPlaneCoordinates '' (physicalHomeomorph F '' S) := by
    rw [image_image, image_image]
    congr 1
  rw [physicalSmoothEnergy_integral hv, he]
  have h := CannonBeltrami.dirichlet_pullback_le F (hF.of_le (by simp))
    (u ∘ complexPlaneCoordinates.symm)
    ((hu.comp complexPlaneCoordinates.symm.contDiff).of_le (by simp))
    (hS.image complexPlaneCoordinates.continuous) hK hD
  rw [hi, ← physicalSmoothEnergy_integral hu] at h
  exact h

end CircleDomainRigidity

end

end OAI
