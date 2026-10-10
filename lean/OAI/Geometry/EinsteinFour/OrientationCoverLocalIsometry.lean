import OAI.Geometry.EinsteinFour.OrientationCoverMetric

namespace OAI

/-! The covering projection preserves the actual local metric matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The inverse sheet chart has the same derivative as the inverse base chart. -/
theorem orientationCover_inverse_chart_mfderiv (x : OrientationCover M) {z : FourSpace}
    (hz : z ∈ (chartAt FourSpace x).target) :
    mfderiv I4 I4 (chartAt FourSpace x).symm z =
      mfderiv I4 I4 (chartAt FourSpace x.proj).symm z := by
  have he : (orientationCoverProjection ∘ (chartAt FourSpace x).symm) =ᶠ[𝓝 z]
      (chartAt FourSpace x.proj).symm := by
    filter_upwards [(chartAt FourSpace x).open_target.mem_nhds hz] with w hw
    exact orientationCoverChart_inverse_proj x hw
  have hd := mfderiv_comp z
    (orientationCover_projection_hasMFDerivAt ((chartAt FourSpace x).symm z)).mdifferentiableAt
    ((mdifferentiable_chart (I := I4) x).symm.mdifferentiableAt hz)
  rw [orientationCover_projection_mfderiv] at hd
  have h := he.mfderiv_eq (I := I4) (I' := I4)
  exact hd.symm.trans h

theorem metricInChart_orientationCoverMetric (g : SmoothMetric M) (x : OrientationCover M)
    {z : FourSpace} (hz : z ∈ (chartAt FourSpace x).target) :
    metricInChart (orientationCoverMetric g) x z = metricInChart g x.proj z := by
  have hd := orientationCover_inverse_chart_mfderiv x hz
  have hp := orientationCoverChart_inverse_proj x hz
  let F : M → (FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) := fun p => g.inner p
  let A : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace x).symm z
  let B : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace x.proj).symm z
  have hab : A = B := hd
  have hp' : ((chartAt FourSpace x).symm z).proj = (chartAt FourSpace x.proj).symm z := hp
  ext i j
  change F (((chartAt FourSpace x).symm z).proj)
    (A (coordinateVector i)) (A (coordinateVector j)) =
    F ((chartAt FourSpace x.proj).symm z) (B (coordinateVector i)) (B (coordinateVector j))
  rw [hp', hab]

end
end PositiveEinsteinFour.Geometry

end OAI
