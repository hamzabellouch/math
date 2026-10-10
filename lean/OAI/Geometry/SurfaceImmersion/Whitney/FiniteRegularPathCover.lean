import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCoverConcat

namespace OAI

/-! Every finite expression of regular smooth path pieces has a finite
closed-interval cover by its actual affine-parametrized smooth pieces. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}

theorem FiniteRegularPath.cover (hγ : FiniteRegularPath J γ) :
    Nonempty (RegularPathCover (J := J) γ) := by
  induction hγ with
  | arc P => exact ⟨RegularPathCover.ofArc P⟩
  | subpath hγ s t ih => exact ⟨ih.some.subpath s t⟩
  | trans hγ hδ ihγ ihδ => exact ⟨ihγ.some.trans ihδ.some⟩
  | cast hγ hx hy ih => exact ⟨ih.some.cast hx hy⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
