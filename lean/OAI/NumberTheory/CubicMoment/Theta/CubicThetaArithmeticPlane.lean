import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticHorizontalTower
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointDifferential
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionDifferential

namespace OAI

/-! The normalized arithmetic expansion as an actual differentiable
function on the positive half-space, with its proved inversion law. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticPlane (p : ℂ × ℝ) : ℂ :=
  cubicThetaSeriesConstant*((p.2^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant cubicThetaArithmeticCoefficient p

lemma cubicThetaArithmeticPlane_section (p : CubicThetaPoint) :
    cubicThetaArithmeticPlane p.val=cubicThetaNormalizedSeriesSection.val p :=
  (cubicThetaNormalizedSeriesSection_apply p).symm

theorem cubicThetaArithmeticPlane_differentiableAt {p : ℂ × ℝ} (hp : 0<p.2) :
    DifferentiableAt ℝ cubicThetaArithmeticPlane p := by
  have hr : DifferentiableAt ℝ (fun q : ℂ × ℝ => q.2^(2/3:ℝ)) p :=
    (Real.hasDerivAt_rpow_const (x:=p.2) (p:=(2/3:ℝ)) (Or.inl hp.ne')).differentiableAt.comp p
      differentiableAt_snd
  have hc : DifferentiableAt ℝ (fun q : ℂ × ℝ => ((q.2^(2/3:ℝ):ℝ):ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hr
  have hn := cubicThetaAngular_differentiableAt (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound 0 hp
  rw [cubicThetaAngularCoefficient_zero] at hn
  exact (hc.const_mul cubicThetaSeriesConstant).add hn

theorem cubicThetaArithmeticPlane_inversion {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaArithmeticPlane (cubicThetaInversion 1 p)=cubicThetaArithmeticPlane p := by
  let x : CubicThetaPoint := ⟨p,hp⟩
  have he := cubicThetaNormalizedSeriesSection_inversion x
  rw [←cubicThetaArithmeticPlane_section,←cubicThetaArithmeticPlane_section] at he
  change cubicThetaArithmeticPlane
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p)=_ at he
  rw [cubicThetaFullInversion_complex,cubicThetaMobius_inversion one_ne_zero hp] at he
  exact he

theorem cubicThetaArithmeticPlane_horizontal_reciprocity {v : ℝ} (hv : 0<v) (h : ℂ) :
    deriv (fun t : ℝ => cubicThetaArithmeticPlane ((t:ℂ)*h,v)) 0=
      deriv (fun t : ℝ => cubicThetaArithmeticPlane ((t:ℂ)*(-star h/(v:ℂ)^2),v⁻¹)) 0 :=
  cubicTheta_inversion_horizontal_deriv (fun _ => cubicThetaArithmeticPlane_differentiableAt)
    (fun _ => cubicThetaArithmeticPlane_inversion) hv h

end CubicFirstMoment

end

end OAI
