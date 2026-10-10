import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicOperator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierCoefficients

namespace OAI

/-! Identification of each nonzero actual Eisenstein row term with a
translated hyperbolic kernel, and its eigenvalue equation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCartesianPoint (x y v : ℝ) : ℂ × ℝ :=
  ((x:ℂ)+(y:ℂ)*Complex.I,v)

lemma cubicThetaRowRadius_cartesian (c d : Eisenstein) (x y v : ℝ) :
    cubicThetaRowRadius c (cubicThetaCartesianPoint x y v) d=
      (x+((d:ℂ)/(c:ℂ)).re)^2+(y+((d:ℂ)/(c:ℂ)).im)^2+v^2 := by
  simp only [cubicThetaRowRadius,cubicThetaCartesianPoint,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,sub_zero]
  ring

theorem cubicThetaEisensteinGridTerm_cartesian {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (d : Eisenstein)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint x y v) s=
      (cubicThetaEisensteinWeight c d*(norm c:ℂ)^(-s))*
        cubicThetaCartesianKernel s (x+((d:ℂ)/(c:ℂ)).re) (y+((d:ℂ)/(c:ℂ)).im) v := by
  rw [cubicThetaEisensteinGridTerm_row hc,
    cubicThetaRowRadius_complex_power hc0 (p:=cubicThetaCartesianPoint x y v) hv,
    cubicThetaRowRadius_cartesian]
  rw [show (cubicThetaCartesianPoint x y v).2=v from rfl,cubicTheta_row_power hv hc0]
  unfold cubicThetaCartesianKernel
  ring

theorem cubicThetaEisensteinGridTerm_eigenvalue {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (d : Eisenstein)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint x y v) s := by
  rw [cubicThetaHyperbolicOperator_congr
    (fun a b t ht => cubicThetaEisensteinGridTerm_cartesian hc hc0 d s a b ht) x y hv,
    cubicThetaHyperbolicOperator_translate,cubicThetaHyperbolicOperator_kernel s _ _ hv,
    cubicThetaEisensteinGridTerm_cartesian hc hc0 d s x y hv]
  ring

end CubicFirstMoment

end

end OAI
