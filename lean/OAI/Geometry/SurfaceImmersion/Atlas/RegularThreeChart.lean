import OAI.Geometry.SurfaceImmersion.Atlas.RegularCurveCoordinates

namespace OAI

/-! Smooth local target charts at an invertible three-dimensional derivative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance regularThreeNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance regularThreeSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

theorem regular_three_chart {F : Base × ℝ → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (z : Base × ℝ) (hreg : Function.Bijective (fderiv ℝ F z)) :
    ∃ e : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3),
      z ∈ e.source ∧ (e : Base × ℝ → ProjectionTarget 3) = F ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  let R : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3 := ContinuousLinearEquiv.ofBijective
    (fderiv ℝ F z) (LinearMap.ker_eq_bot.mpr hreg.1) (LinearMap.range_eq_top.mpr hreg.2)
  have hd : HasFDerivAt F R.toContinuousLinearMap z :=
    (hF.differentiable (by simp) z).hasFDerivAt
  let e₀ := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  let W : Set (Base × ℝ) := {p | IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ F p))}
  have hcont : Continuous (fun p => R.symm.toContinuousLinearMap.comp (fderiv ℝ F p)) :=
    continuous_const.clm_comp (hF.continuous_fderiv (by simp))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have hzW : z ∈ W := ContinuousLinearMap.isUnit_iff_bijective.mpr (R.symm.bijective.comp hreg)
  let e := e₀.restrOpen W hW
  have he : (e : Base × ℝ → ProjectionTarget 3) = F := rfl
  refine ⟨e,⟨hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),hzW⟩,he,?_⟩
  intro y hy
  obtain ⟨u,hu⟩ := (e.map_target hy).2
  let D := (ContinuousLinearEquiv.ofUnit u).trans R
  have hde : D.toContinuousLinearMap = fderiv ℝ F (e.symm y) := by
    apply ContinuousLinearMap.ext
    intro v
    change R ((u : (Base × ℝ) →L[ℝ] (Base × ℝ)) v) = _
    rw [hu]
    exact R.apply_symm_apply _
  have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
    rw [he,hde]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hF.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
