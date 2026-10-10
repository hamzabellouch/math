import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.ScalarRegularity06
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI


section

/-! Change of variables for a compact amplitude in an actual normal chart.
The normalization factor of the manifold measure remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem heatNormalScalarLift_integral_chart (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (J : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hJ : ∀ x ∈ C.source, HasFDerivAt (fun y => chartAt FourSpace c (C y)) (J x) x)
    (ψ : FourSpace → ℝ) :
    (∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g) =
      (normalizedChartFactor g).toReal * ∫ x in C.source,
        |(J x).det| * chartVolumeDensity g c (chartAt FourSpace c (C x)) * ψ x := by
  classical
  let A := chartAt FourSpace c
  let T := C.trans A
  have hTs : T.source = C.source := by
    ext x
    change (x ∈ C.source ∧ C x ∈ A.source) ↔ x ∈ C.source
    exact ⟨And.left, fun hx => ⟨hx, hCt (C.map_source hx)⟩⟩
  let Q := fun z => chartVolumeDensity g c z * heatNormalScalarLift C ψ (A.symm z)
  let H := A.target.indicator Q
  have hHz (z : FourSpace) (hz : z ∉ T.target) : H z = 0 := by
    by_cases ha : z ∈ A.target
    · have hc : A.symm z ∉ C.target := fun hc => hz ⟨ha, hc⟩
      simp only [H, indicator_of_mem ha, Q, heatNormalScalarLift,
        ite_eq_right_iff, mul_eq_zero]
      exact Or.inr (by simp [hc])
    · exact indicator_of_notMem ha Q
  have hHT : (∫ z in A.target, Q z) = ∫ z in T.target, H z := by
    rw [← integral_indicator A.open_target.measurableSet]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hHz).symm
  have hder (x : FourSpace) (hx : x ∈ T.source) : HasFDerivAt T (J x) x :=
    hJ x (hTs ▸ hx)
  have hzero (y : M) (hy : y ∉ A.source) : heatNormalScalarLift C ψ y = 0 := by
    have hc : y ∉ C.target := fun hc => hy (hCt hc)
    simp [heatNormalScalarLift, hc]
  rw [normalizedVolume_integral_chart g c _ hzero]
  change (normalizedChartFactor g).toReal * (∫ z in A.target, Q z) = _
  rw [hHT, integral_target_eq_integral_abs_det_fderiv_smul volume hder, hTs]
  congr 1
  apply setIntegral_congr_fun C.open_source.measurableSet
  intro x hx
  have ha : T x ∈ A.target := A.map_source (hCt (C.map_source hx))
  have hi : A.symm (T x) = C x := A.left_inv (hCt (C.map_source hx))
  have hH : H (T x) = chartVolumeDensity g c (T x) * ψ x := by
    change A.target.indicator Q (T x) = _
    rw [indicator_of_mem ha]
    change chartVolumeDensity g c (T x) * heatNormalScalarLift C ψ (A.symm (T x)) = _
    rw [hi, heatNormalScalarLift_source C ψ hx]
  change |(J x).det| • H (T x) = _
  rw [hH, smul_eq_mul]
  change |(J x).det| * (chartVolumeDensity g c (chartAt FourSpace c (C x)) * ψ x) = _
  ring

end
end PositiveEinsteinFour.Geometry
end

end OAI
