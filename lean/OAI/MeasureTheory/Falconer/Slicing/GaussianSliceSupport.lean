import OAI.MeasureTheory.Falconer.Slicing.OrientedSlice
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedMass
import OAI.MeasureTheory.Falconer.Slicing.GaussianKernelCoordinates

namespace OAI

/-! # Chart support for the retained Gaussian point and direction laws -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_pruned_point_bounded_coordinates
    (μ : Measure (Space d)) (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞)
    {D L : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hL : 0 < L) (hDL : 4*D ≤ L) :
    ∀ᵐ x ∂((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))),
      ‖L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)‖ ≤ 1/4 := by
  filter_upwards [ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ A z δ hμ)] with x hx
  have he : ‖e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)‖ ≤ D := by
    rw [e.norm_map]
    exact ((gaussianRowMap A).ker.norm_starProjection_apply_le x).trans hx
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL),mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ hL).mpr
  linarith

theorem gaussian_pruned_direction_unit_chart
    (ν : Measure (Sphere d)) (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (w₀ : Sphere d) {K δ₀ ρ : ℝ} (hK : 0 ≤ K)
    (hν : ∀ᵐ (w : Sphere d) ∂ν, dist (w:Space d) (w₀:Space d) ≤ ρ)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hsmall₀ : δ₀ < 1)
    (hw₀ : w₀ ∈ directionSliceBand (gaussianRowMap A).ker δ₀)
    (haxis : normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w₀:Space d))) =
      EuclideanSpace.basisFun (Fin 2) ℝ 0)
    (hchart : 2*(K*((h:ℝ)*δ))+ρ+2*δ₀ ≤ 1/4) :
    ∀ᵐ (w : Sphere d) ∂((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  have hbase : ∀ᵐ (w : Sphere d) ∂((gaussianDirectionSliceMeasure ν A δ).restrict
      (gaussianDirectionGood ν δ r TD M A)), dist (w:Space d) (w₀:Space d) ≤ ρ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν) _)
  have hband : ∀ᵐ (w : Sphere d) ∂((gaussianDirectionSliceMeasure ν A δ).restrict
      (gaussianDirectionGood ν δ r TD M A)), w ∈ gaussianDirectionBand A δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure
      (ae_restrict_mem (gaussianDirectionBand_measurable A δ)) _)
  filter_upwards [hbase,hband] with w hclose hw
  have hp := gaussian_direction_kernel_nonzero A hK hbound hsmall hw
  have hv : (gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d) ≠ 0 :=
    fun hz => hp (congrArg Subtype.val hz)
  have he : e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)) ≠ 0 :=
    fun hz => hv (e.injective (by simpa only [map_zero] using hz))
  refine ⟨norm_normalize he,?_⟩
  have hc := oriented_slice_direction_distance (gaussianRowMap A).ker e hsmall hsmall₀
    (gaussian_direction_band_kernel_distance A hK hbound hw) hw₀ hclose
  rw [haxis] at hc
  exact hc.trans hchart

end Falconer

end OAI
