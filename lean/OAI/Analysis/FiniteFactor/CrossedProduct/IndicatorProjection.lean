import OAI.Analysis.FiniteFactor.CrossedProduct.ScalarCenter
import OAI.Analysis.FiniteFactor.CrossedProduct.MultiplicationAdjoint
import OAI.Analysis.FiniteFactor.CrossedProduct.SmallPartitionSets

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceIndicatorProjection (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  sourcePi θ (sourceBaseIndicator A hA)

theorem sourceIndicatorProjection_mem (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    sourceIndicatorProjection θ A hA ∈ sourceAlgebra θ := sourcePi_mem θ _

theorem sourceIndicatorProjection_projection (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    IsStarProjection (sourceIndicatorProjection θ A hA) := by
  classical
  let g := sourceBaseIndicator A hA
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [sourcePi_apply_ae θ g (sourcePi θ g f),sourcePi_apply_ae θ g f] with z hh hf
    change (sourcePi θ g (sourcePi θ g f)) z = (sourcePi θ g f) z
    rw [hh,hf]
    by_cases hz : coordinateRotate θ z.2 z.1 ∈ A <;> simp [sourcePiSymbol,g,sourceBaseIndicator,hz]
  · change star (sourcePi θ g) = sourcePi θ g
    rw [sourcePi_star]
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [sourcePi_apply_ae θ (sourceBaseStar g) f,sourcePi_apply_ae θ g f] with z hs hf
    rw [hs,hf]
    by_cases hz : coordinateRotate θ z.2 z.1 ∈ A <;> simp [sourcePiSymbol,sourceBaseStar,g,sourceBaseIndicator,hz]

/-- The projection's trace is the measure of its original base event. -/
theorem sourceIndicatorProjection_trace (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    sourceVacuumFunctional (sourceIndicatorProjection θ A hA) =
      ((sourceBaseMeasure A).toReal : ℂ) := by
  rw [sourceVacuumFunctional_matrixIntegral]
  have he : sourceMatrixEntry (sourceIndicatorProjection θ A hA) 0 0 =ᵐ[sourceBaseMeasure]
      A.indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [sourceMatrixEntry_pi θ (sourceBaseIndicator A hA) 0,sourceSamplingHaar_cube] with x hx hc
    have hr : coordinateRotate θ 0 x = x := by
      funext i
      simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
    simpa [sourceIndicatorProjection,sourceBaseIndicator,hr] using hx 0
  rw [integral_congr_ae he,integral_indicator hA]
  simp [measureReal_def]

/-- A genuine finite partition of the identity inside the original algebra. -/
theorem sourceIndicatorProjection_partition_sum (θ : SourceCoordinate → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ j : Fin n, sourceIndicatorProjection θ (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change (∑ j : Fin n, sourceIndicatorProjection θ (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j)) f = f
  rw [sum_apply]
  apply Lp.ext
  have hall := ae_all_iff.mpr (fun j : Fin n =>
    sourcePi_apply_ae θ (sourceBaseIndicator (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j)) f)
  filter_upwards [sourceHilbert_sum_coe Finset.univ (fun j : Fin n =>
    sourceIndicatorProjection θ (sourceSmallPartitionSet n j) (sourceSmallPartitionSet_measurable n j) f),hall]
    with z hs ha
  rw [hs]
  change (∑ j : Fin n, (sourcePi θ (sourceBaseIndicator (sourceSmallPartitionSet n j)
    (sourceSmallPartitionSet_measurable n j)) f) z) = f z
  simp_rw [ha]
  change (∑ j : Fin n, (sourceSmallPartitionSet n j).indicator (fun _ => (1 : ℂ))
    (coordinateRotate θ z.2 z.1) * f z) = f z
  rw [← Finset.sum_mul,sourceSmallPartition_indicator_sum n hn _
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,one_mul]

end
end FiniteFactor

end OAI
