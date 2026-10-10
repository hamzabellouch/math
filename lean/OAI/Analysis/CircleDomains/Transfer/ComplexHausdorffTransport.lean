import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals
import OAI.Analysis.CircleDomains.Sobolev.SobolevScalarCoarea

namespace OAI

/-! The physical coordinate chart is an isometry, including for the
Hausdorff-length measures on the full pointwise coarea levels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def complexPlaneIsometry : EuclideanPlane ≃ᵢ ℂ where
  toEquiv := complexPlaneCoordinates.toEquiv
  isometry_toFun := by
    apply isometry_iff_dist_eq.mpr
    intro p q
    change dist (complexPlaneCoordinates p) (complexPlaneCoordinates q) = dist p q
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, complexPlaneCoordinates_norm]

 theorem complexPlaneCoordinates_hausdorff_preserving :
    MeasurePreserving complexPlaneCoordinates (μH[1] : Measure EuclideanPlane) (μH[1] : Measure ℂ) :=
  complexPlaneIsometry.measurePreserving_hausdorffMeasure 1

 theorem complex_hausdorff_set_integral (E : Set ℂ) (q : ℂ → ℝ≥0∞) :
    (∫⁻ p in complexPlaneCoordinates ⁻¹' E, q (complexPlaneCoordinates p)
      ∂(μH[1] : Measure EuclideanPlane)) = ∫⁻ z in E, q z ∂(μH[1] : Measure ℂ) :=
  complexPlaneCoordinates_hausdorff_preserving.setLIntegral_comp_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding q E

 theorem complex_sobolev_level_integral (E : Set ℂ) (v : ℂ → ℝ) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E)
      (v ∘ complexPlaneCoordinates) (q ∘ complexPlaneCoordinates) t =
      ∫⁻ z in E ∩ {z | v z = t}, q z ∂(μH[1] : Measure ℂ) := by
  exact complex_hausdorff_set_integral (E ∩ {z | v z = t}) q

end CircleDomainRigidity

end

end OAI
