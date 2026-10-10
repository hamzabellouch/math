import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMetricDerivative

namespace OAI

/-! Polarization of the derivative scale proves invariance of the actual
hyperbolic tangent inner product. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaEuclideanPairing (u v : ℂ × ℝ) : ℝ :=
  u.1.re*v.1.re+u.1.im*v.1.im+u.2*v.2

def cubicThetaHyperbolicPairing (p u v : ℂ × ℝ) : ℝ :=
  cubicThetaEuclideanPairing u v/p.2^2

lemma cubicThetaRadius_add (u v : ℂ × ℝ) :
    cubicThetaRadius (u+v)=cubicThetaRadius u+cubicThetaRadius v+
      2*cubicThetaEuclideanPairing u v := by
  simp only [cubicThetaRadius,cubicThetaEuclideanPairing,Prod.fst_add,Prod.snd_add,
    Complex.normSq_apply,Complex.add_re,Complex.add_im]
  ring

lemma cubicThetaHyperbolicPairing_invariant (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0<p.2) (u v : ℂ × ℝ) :
    cubicThetaHyperbolicPairing (cubicThetaMobius g p)
      (fderiv ℝ (cubicThetaMobius g) p u) (fderiv ℝ (cubicThetaMobius g) p v)=
      cubicThetaHyperbolicPairing p u v := by
  have hu := cubicThetaMobius_derivative_scale g hp u
  have hv := cubicThetaMobius_derivative_scale g hp v
  have huv := cubicThetaMobius_derivative_scale g hp (u+v)
  rw [map_add,cubicThetaRadius_add,cubicThetaRadius_add] at huv
  unfold cubicThetaHyperbolicPairing
  apply (div_eq_div_iff (pow_ne_zero 2 (cubicThetaMobius_height_pos g hp).ne')
    (pow_ne_zero 2 hp.ne')).mpr
  nlinarith [hu,hv,huv]

end CubicFirstMoment

end

end OAI
