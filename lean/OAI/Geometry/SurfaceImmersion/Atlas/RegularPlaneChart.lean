import OAI.Geometry.SurfaceImmersion.Atlas.PlaneCurveCoordinates

namespace OAI

/-! A local smooth plane chart at an invertible derivative, retaining
its actual globally defined coordinate map. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem regular_plane_chart {F : Base → Base} (hF : ContDiff ℝ ∞ F)
    (p : Base) (hreg : Function.Bijective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (e : Base → Base) = F ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let R : Base ≃L[ℝ] Base := ContinuousLinearEquiv.ofBijective (fderiv ℝ F p)
    (LinearMap.ker_eq_bot.mpr hreg.1) (LinearMap.range_eq_top.mpr hreg.2)
  have hd : HasFDerivAt F R.toContinuousLinearMap p := (hF.differentiable (by simp) p).hasFDerivAt
  let e₀ := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  let W : Set Base := {x | IsUnit (fderiv ℝ F x)}
  have hW : IsOpen W := Units.isOpen.preimage (hF.continuous_fderiv (by simp))
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = F := rfl
  refine ⟨e,⟨hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),
    ContinuousLinearMap.isUnit_iff_bijective.mpr hreg⟩,he,?_⟩
  intro y hy
  obtain ⟨u,hu⟩ := (e.map_target hy).2
  let D := ContinuousLinearEquiv.ofUnit u
  have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
    rw [he]
    convert (hF.differentiable (by simp) _).hasFDerivAt using 1
    exact hu
  exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hF.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
