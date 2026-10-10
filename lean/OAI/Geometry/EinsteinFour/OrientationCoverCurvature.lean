import OAI.Geometry.EinsteinFour.OrientationCoverLocalIsometry

namespace OAI

/-! Curvature and Einstein normalization are preserved by the actual cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem partialDeriv_eq_of_eventuallyEq {f h : FourSpace → ℝ}
    {z : FourSpace} (he : f =ᶠ[𝓝 z] h) (i : Fin 4) :
    partialDeriv f i z = partialDeriv h i z :=
  congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq

theorem christoffel_orientationCoverMetric (g : SmoothMetric M) (x : OrientationCover M)
    {z : FourSpace} (hz : z ∈ (chartAt FourSpace x).target) (k i j : Fin 4) :
    christoffel (orientationCoverMetric g) x z k i j = christoffel g x.proj z k i j := by
  have hd (a b d : Fin 4) :
      partialDeriv (fun w => metricInChart (orientationCoverMetric g) x w a b) d z =
        partialDeriv (fun w => metricInChart g x.proj w a b) d z := by
    apply partialDeriv_eq_of_eventuallyEq
    filter_upwards [(chartAt FourSpace x).open_target.mem_nhds hz] with w hw
    exact congrArg (fun A => A a b) (metricInChart_orientationCoverMetric g x hw)
  simp only [christoffel, metricInChart_orientationCoverMetric g x hz, hd]

theorem curvatureComponent_orientationCoverMetric (g : SmoothMetric M)
    (x : OrientationCover M) {z : FourSpace} (hz : z ∈ (chartAt FourSpace x).target)
    (l i j k : Fin 4) :
    curvatureComponent (orientationCoverMetric g) x z l i j k =
      curvatureComponent g x.proj z l i j k := by
  have hd (a b c d : Fin 4) :
      partialDeriv (fun w => christoffel (orientationCoverMetric g) x w a b c) d z =
        partialDeriv (fun w => christoffel g x.proj w a b c) d z := by
    apply partialDeriv_eq_of_eventuallyEq
    filter_upwards [(chartAt FourSpace x).open_target.mem_nhds hz] with w hw
    exact christoffel_orientationCoverMetric g x hw a b c
  simp only [curvatureComponent, hd, christoffel_orientationCoverMetric g x hz]

theorem ricciInChart_orientationCoverMetric (g : SmoothMetric M) (x : OrientationCover M)
    {z : FourSpace} (hz : z ∈ (chartAt FourSpace x).target) (i j : Fin 4) :
    ricciInChart (orientationCoverMetric g) x z i j = ricciInChart g x.proj z i j := by
  simp only [ricciInChart, curvatureComponent_orientationCoverMetric g x hz]

theorem sectionalNumerator_orientationCoverMetric (g : SmoothMetric M)
    (x : OrientationCover M) {z : FourSpace} (hz : z ∈ (chartAt FourSpace x).target)
    (u v : FourSpace) :
    sectionalNumerator (orientationCoverMetric g) x z u v =
      sectionalNumerator g x.proj z u v := by
  simp only [sectionalNumerator, metricInChart_orientationCoverMetric g x hz,
    curvatureComponent_orientationCoverMetric g x hz]

theorem isEinstein_orientationCoverMetric (g : SmoothMetric M) (hg : IsEinstein g) :
    IsEinstein (orientationCoverMetric g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, fun x i j => ?_⟩
  have hx := (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)
  rw [ricciInChart_orientationCoverMetric g x hx,
    metricInChart_orientationCoverMetric g x hx]
  rw [show chartAt FourSpace x x = chartAt FourSpace x.proj x.proj from
    orientationCoverChart_apply x x]
  exact hc x.proj i j

theorem positive_orientationCoverMetric (g : SmoothMetric M)
    (hg : HasPositiveSectionalCurvature g) :
    HasPositiveSectionalCurvature (orientationCoverMetric g) := by
  intro x u v huv
  have hx := (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)
  rw [sectionalNumerator_orientationCoverMetric g x hx]
  rw [show chartAt FourSpace x x = chartAt FourSpace x.proj x.proj from
    orientationCoverChart_apply x x]
  exact hg x.proj u v huv

end
end PositiveEinsteinFour.Geometry

end OAI
