import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowHeightChain

namespace OAI

/-! The incoming term for each actual arithmetic row satisfies the
spectral equation, with the transported compact annular forcing. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

theorem cubicThetaIncomingTerm_equation (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingTerm r (cubicThetaCartesianPoint x y v) s+
        star r.phase*cubicThetaIncomingForcing s
          (r.height (cubicThetaCartesianPoint x y v)) := by
  have hp : 0<cubicThetaRowHeightCoordinates r x y v := r.height_pos hv
  have hf : ContDiffAt ℝ 2 (fun t : ℝ => cubicThetaCuspCutoff t*(t:ℂ)^s)
      (cubicThetaRowHeightCoordinates r x y v) :=
    (cubicThetaCuspCutoff_smooth.contDiffAt.mul
      (cubicThetaHeightPower_analytic s hp).contDiffAt).of_le (by norm_num)
  have he : (fun a b t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s)=
      (fun a b t => star r.phase*(cubicThetaCuspCutoff
        (cubicThetaRowHeightCoordinates r a b t)*
          (cubicThetaRowHeightCoordinates r a b t:ℂ)^s)) := by
    funext a b t
    unfold cubicThetaIncomingTerm cubicThetaEisensteinTerm cubicThetaRowHeightCoordinates
    ring
  rw [he,cubicThetaHyperbolicOperator_const_mul,
    cubicThetaRowHeight_operator r x y hv hf,cubicThetaCutoffIncoming_equation s 0 0 hp]
  unfold cubicThetaIncomingTerm cubicThetaEisensteinTerm cubicThetaRowHeightCoordinates
  ring

end CubicFirstMoment

end

end OAI
