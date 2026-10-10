import OAI.Geometry.NodalSets.Charts.ChartOperatorIdentity

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem inversePulledForm_transform
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (a : Coord →L[ℝ] ℝ) :
    inversePulledForm g p x a =
      J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x))
        (a.comp J.symm.toContinuousLinearMap)) := by
  apply positive_metric_injective (pulledForm g p x) (pulledForm_positive g p x hp J hJ)
  ext v
  rw [show pulledForm g p x (inversePulledForm g p x a) v = a v from
    inverse_form_pair _ (pulledForm_positive g p x hp J hJ) a v]
  change a v = g (rawQuadratic p x)
    (fderiv ℝ (rawQuadratic p) x (J.symm _)) (fderiv ℝ (rawQuadratic p) x v)
  rw [hJ]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [inverse_form_pair _ hp]
  simp

theorem inversePulledForm_comp_fderiv
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : Coord → ℝ) (hu : DifferentiableAt ℝ u (rawQuadratic p x)) :
    inversePulledForm g p x (fderiv ℝ (u ∘ rawQuadratic p) x) =
      J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x))
        (fderiv ℝ u (rawQuadratic p x))) := by
  rw [inversePulledForm_transform g p x hp J hJ]
  rw [fderiv_comp x hu ((rawQuadratic_smooth.comp
    (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x)]
  rw [hJ]
  congr 2
  ext v
  simp

end
end Yau.Geometry

end OAI
