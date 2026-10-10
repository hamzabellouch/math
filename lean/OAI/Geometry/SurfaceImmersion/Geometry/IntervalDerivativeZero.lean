import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! A smooth scalar coordinate vanishing on a one-sided interval has
zero derivative at its endpoint as well. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem deriv_zero_of_interval_germ {g : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hg : DifferentiableAt ℝ g t)
    (he : g =ᶠ[𝓝[Icc a b] t] fun _ => 0) : deriv g t = 0 := by
  have hz : HasDerivWithinAt g 0 (Icc a b) t :=
    (hasDerivWithinAt_const t (Icc a b) (0:ℝ)).congr_of_eventuallyEq_of_mem he ht
  exact ((uniqueDiffOn_Icc hab) t ht).eq_deriv (Icc a b) hg.hasDerivAt.hasDerivWithinAt hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
