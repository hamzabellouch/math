import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorEnergy
import OAI.Analysis.CircleDomains.Sobolev.MollificationEnergy

namespace OAI

/-! Exact complex-chart energy of a smooth physical scalar, and its
convergence under positive mollification. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complex_scalar_energy_pointwise {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : EuclideanPlane) :
    ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)‖^2 =
      (fderiv ℝ u x (EuclideanSpace.single 0 1))^2 +
      (fderiv ℝ u x (EuclideanSpace.single 1 1))^2 := by
  rw [complexCovector_norm_sq]
  change (fderiv ℝ (fun z => u (complexPlaneCoordinates.symm z))
      (complexPlaneCoordinates x) 1)^2 +
    (fderiv ℝ (fun z => u (complexPlaneCoordinates.symm z))
      (complexPlaneCoordinates x) Complex.I)^2 = _
  rw [← complexPlaneCoordinates_zero, physical_complex_partial hu,
    ← complexPlaneCoordinates_one, physical_complex_partial hu]

 theorem complex_scalar_energy_integral {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (U : Set ℂ) :
    (∫ z in U, ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2) =
      ∫ x in complexPlaneCoordinates ⁻¹' U,
        (fderiv ℝ u x (EuclideanSpace.single 0 1))^2 +
        (fderiv ℝ u x (EuclideanSpace.single 1 1))^2 := by
  rw [← complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding
    (fun z => ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2) U]
  apply integral_congr_ae
  exact Eventually.of_forall (complex_scalar_energy_pointwise hu)

 theorem complex_mollification_energy_tendsto {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hs : HasCompactSupport u) (U : Set ℂ) :
    Tendsto (fun n => ∫ z in U,
      ‖fderiv ℝ ((planarMollification u n) ∘ complexPlaneCoordinates.symm) z‖^2)
      atTop (𝓝 (∫ x in complexPlaneCoordinates ⁻¹' U,
        hu.weakGrad x 0^2 + hu.weakGrad x 1^2)) := by
  have hL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  have ht := planarMollification_energy_tendsto hu hs (complexPlaneCoordinates ⁻¹' U)
  exact ht.congr' (Eventually.of_forall (fun n =>
    (complex_scalar_energy_integral (planarMollification_smooth
      (hL.locallyIntegrable (by norm_num)) n) U).symm))

end CircleDomainRigidity

end

end OAI
