import OAI.Analysis.CircleDomains.Uniformization.SquareAverageLimit
import OAI.Analysis.CircleDomains.Sobolev.AverageSquareBound

namespace OAI

/-! A square's mean oscillation squared is bounded by its actual local
Sobolev energy. The radius cancels against the square's area. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_partial_coordinate_memLp {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (i : Fin 2) :
    MemLp (fun p => V (euclideanPlaneCoordinates.symm p) i) 2 (volume.restrict K) := by
  have hKC := hK.image euclideanPlaneCoordinates.symm.continuous
  obtain ⟨R,hR⟩ := hKC.isBounded.subset_ball 0
  have hi := (hLp R i).mono_measure (Measure.restrict_mono hR le_rfl)
  have hP := euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage hKC.measurableSet
  have hpre : euclideanPlaneCoordinates.symm ⁻¹' (euclideanPlaneCoordinates.symm '' K) = K :=
    Set.preimage_image_eq K euclideanPlaneCoordinates.symm.injective
  rw [hpre] at hP
  exact hi.comp_measurePreserving hP

lemma locally_sobolev_square_oscillation_sq {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    (⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
      squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c r|)^2 ≤
    ∫ p in coordinateSquare c r,
      (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2 := by
  let G := fun p => |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|
  let μ := volume.restrict (coordinateSquare c r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (coordinateSquare_compact c r).measure_lt_top.ne
  let : NeZero μ := ⟨by simpa [μ] using coordinateSquare_volume_ne_zero c hr⟩
  have hG : MemLp G 2 μ :=
    (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 0).norm.add
      (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 1).norm
  have hsq := sq_average_le_average_sq (hG.integrable (by norm_num))
    ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG)
  have hP := locally_sobolev_square_poincare hu hw hLp c hr
  have hA : 0 ≤ ⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
      squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c r| :=
    average_nonneg (fun _ => abs_nonneg _)
  have hle := pow_le_pow_left₀ hA hP 2
  calc
    _ ≤ (2*r)^2 * (⨍ p, G p ∂μ)^2 := by simpa only [mul_pow] using hle
    _ ≤ (2*r)^2 * (⨍ p, G p^2 ∂μ) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by
      rw [average_eq, show μ.real univ = 4*r^2 by
        change (volume.restrict (coordinateSquare c r)).real univ = 4*r^2
        rw [measureReal_restrict_apply_univ, coordinateSquare_real_volume c hr.le], smul_eq_mul]
      dsimp only [μ, G]
      field_simp [hr.ne']
      ring

end CircleDomainRigidity

end

end OAI
