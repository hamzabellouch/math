import OAI.Geometry.EinsteinFour.OrientationCoverProjection

namespace OAI

/-! A continuous lift through the orientation cover inherits smoothness from
its projection, because its local chart is exactly the base chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}

theorem contMDiffAt_orientationCover_lift {f : N → OrientationCover M} {x : N}
    (hc : ContinuousAt f x)
    (hf : ContMDiffAt J I4 n (orientationCoverProjection ∘ f) x) :
    ContMDiffAt J I4 n f x := by
  obtain ⟨_, hd⟩ := contMDiffAt_iff.mp hf
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  have he : writtenInExtChartAt J I4 x f =
      writtenInExtChartAt J I4 x (orientationCoverProjection ∘ f) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
    exact congrArg I4 (orientationCoverChart_apply (f x) (f ((extChartAt J x).symm z)))
  change ContDiffWithinAt ℝ n (writtenInExtChartAt J I4 x f) (range J) (extChartAt J x x)
  rw [he]
  exact hd

theorem contMDiff_orientationCover_lift {f : N → OrientationCover M}
    (hc : Continuous f) (hf : ContMDiff J I4 n (orientationCoverProjection ∘ f)) :
    ContMDiff J I4 n f :=
  fun x => contMDiffAt_orientationCover_lift hc.continuousAt (hf x)

end
end PositiveEinsteinFour.Geometry

end OAI
