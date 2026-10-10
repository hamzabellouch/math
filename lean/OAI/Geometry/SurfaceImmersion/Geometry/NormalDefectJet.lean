import OAI.Geometry.SurfaceImmersion.Geometry.NormalFrameJet
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionJet

namespace OAI

/-! Differentiating the genuine normal defect at a singular point.
The derivative of the moving frame cancels because the vertical column is zero. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalDefect_fderiv_at_zero {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Fin 3 → ℝ) (p : Base)
    (hu : transverseDerivative φ p ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ p ≠ a)
    (hz : fderiv ℝ φ p (![0,1] : Base) = 0) :
    fderiv ℝ (normalDefect φ a) p = (ContinuousLinearMap.fst ℝ Base ℝ).comp
      ((curveNormalLinear (transverseDerivative φ p) a).inverse.comp
        (fderiv ℝ (fun x => coordinateDifferential φ x (![0,1] : Base)) p)) := by
  let J := fun x => (curveNormalLinear (transverseDerivative φ x) a).inverse
  let W := fun x => coordinateDifferential φ x (![0,1] : Base)
  have hU := transverseDerivative_smooth hφ
  have hcross : ContDiff ℝ ∞ (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  have hframe : ContDiff ℝ ∞ (fun x => curveNormalLinear (transverseDerivative φ x) a) :=
    ((contDiff_const.smulRight hU).add contDiff_const).add (contDiff_const.smulRight hcross)
  have hJ : ContDiffAt ℝ ∞ J p := by
    change ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse ∘
      (fun x => curveNormalLinear (transverseDerivative φ x) a)) p
    exact (curveNormalLinear_invertible hu ha).contDiffAt_map_inverse.comp p hframe.contDiffAt
  have hW : ContDiff ℝ ∞ W := (coordinateDifferential_smooth hφ).clm_apply contDiff_const
  have hWp : W p = 0 := by simp [W,coordinateDifferential,hz]
  have hd := (hJ.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hW.differentiable (by simp) p).hasFDerivAt
  have he := hd.fst.fderiv
  have hfun : (fun x => (J x (W x)).1) = normalDefect φ a := rfl
  rw [hfun] at he
  apply ContinuousLinearMap.ext
  intro v
  have hev := congrArg (fun L => L v) he
  simpa [J,W,hWp,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] using hev

lemma normalDefect_jet_bijective {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Fin 3 → ℝ) (p : Base)
    (hu : transverseDerivative φ p ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ p ≠ a)
    (hz : fderiv ℝ φ p (![0,1] : Base) = 0)
    (hK : Function.Bijective (directionBlock
      (fderiv ℝ (fun x => coordinateDifferential φ x (![0,1] : Base)) p)
      (transverseDerivative φ p))) :
    Function.Bijective (fderiv ℝ (normalDefect φ a) p) := by
  rw [normalDefect_fderiv_at_zero hφ a p hu ha hz]
  exact normal_frame_jet_bijective hu ha _ hK

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
