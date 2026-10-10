import OAI.Geometry.EinsteinFour.OrientationCoverCharts

namespace OAI

/-! The projection of the actual orientation cover is smooth and its derivative
is the identity in the preferred tangent coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_projection_inCharts (x : OrientationCover M) :
    writtenInExtChartAt I4 I4 x orientationCoverProjection =ᶠ[
      𝓝 (extChartAt I4 x x)] id := by
  have hx : orientationCoverChart x x ∈ (orientationCoverChart x).target :=
    (orientationCoverChart x).map_source (orientationCoverChart_mem x)
  have hcenter : extChartAt I4 x x = orientationCoverChart x x := by
    simp only [extChartAt_coe, I4, modelWithCornersSelf_coe, Function.comp_apply, id_eq]
    rfl
  rw [hcenter]
  filter_upwards [(orientationCoverChart x).open_target.mem_nhds hx] with z hz
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, I4,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
  change chartAt FourSpace x.proj (((orientationCoverChart x).symm z).proj) = z
  rw [orientationCoverChart_inverse_proj x hz]
  exact (chartAt FourSpace x.proj).right_inv hz.1

theorem orientationCover_projection_smooth :
    ContMDiff I4 I4 ∞ (orientationCoverProjection (M := M)) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨orientationCover_isCoveringMap.continuous.continuousAt, ?_⟩
  have h : ContDiffAt ℝ ∞ (writtenInExtChartAt I4 I4 x orientationCoverProjection)
      (extChartAt I4 x x) :=
    contDiffAt_id.congr_of_eventuallyEq (orientationCover_projection_inCharts x)
  exact h.contDiffWithinAt

theorem orientationCover_projection_hasMFDerivAt (x : OrientationCover M) :
    HasMFDerivAt I4 I4 orientationCoverProjection x (ContinuousLinearMap.id ℝ FourSpace) := by
  refine ⟨orientationCover_isCoveringMap.continuous.continuousAt, ?_⟩
  have h := (hasFDerivAt_id (𝕜 := ℝ) (extChartAt I4 x x)).congr_of_eventuallyEq
    (orientationCover_projection_inCharts x)
  exact h.hasFDerivWithinAt

@[simp] theorem orientationCover_projection_mfderiv (x : OrientationCover M) :
    mfderiv I4 I4 orientationCoverProjection x = ContinuousLinearMap.id ℝ FourSpace :=
  (orientationCover_projection_hasMFDerivAt x).mfderiv

end
end PositiveEinsteinFour.Geometry

end OAI
