import OAI.Geometry.NodalSets.Elliptic.TransportedOperator

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma actual_coordinate_residual_smoothOn
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam Coord) (U : Set Coord)
    (hJ : ∀ x ∈ U, ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (hwp : ∀ x ∈ U, 0 < w (rawQuadratic p x))
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (lam : ℂ) :
    ContDiffOn ℝ ∞ (fun x ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
      (fun j ↦ complexDrift g w j p) u x + lam*u x) U := by
  have hG (i j : Fin 4) : ContDiffOn ℝ ∞ (complexPrincipal g i j p) U := by
    intro x hx
    obtain ⟨J,hJe⟩ := hJ x hx
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((chartPrincipal_smooth_at g hg p x (hp _) J hJe i j).comp x
        (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt
  have hB (j : Fin 4) : ContDiffOn ℝ ∞ (complexDrift g w j p) U := by
    intro x hx
    obtain ⟨J,hJe⟩ := hJ x hx
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((chartDrift_smooth_at g hg w hw p x (hp _) (hwp x hx) J hJe j).comp x
        (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt
  unfold smoothSecondOrder
  exact ((ContDiffOn.sum (fun i _ ↦ ContDiffOn.sum (fun j _ ↦
    (hG i j).mul (coordPartial_contDiff (coordPartial_contDiff hu j) i).contDiffOn))).add
      (ContDiffOn.sum (fun i _ ↦ (hB i).mul (coordPartial_contDiff hu i).contDiffOn))).add
        (contDiffOn_const.mul hu.contDiffOn)

end
end Yau.Geometry

end OAI
