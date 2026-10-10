import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEven

namespace OAI

/-! The concrete theta and auxiliary Fourier series from DR v3 (5.6),
(5.7), (5.13) and (5.14), with their proved analytic properties. Modular
transformation identities remain to be established. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaAuxiliarySeries (j : Fin 3) (p : ℂ × ℝ) : ℂ :=
  cubicThetaNonconstant (cubicThetaCuspCoefficient j) p

def cubicThetaConstant : ℝ := 3^(5/2:ℝ)/2

def cubicThetaFunction (p : ℂ × ℝ) : ℂ :=
  (cubicThetaConstant*p.2^(2/3:ℝ):ℝ)+cubicThetaAuxiliarySeries 0 p

lemma cubicThetaAuxiliarySeries_continuousAt (j : Fin 3) {p : ℂ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (cubicThetaAuxiliarySeries j) p :=
  cubicThetaNonconstant_continuousAt (by norm_num : (0:ℝ) ≤ 81)
    (cubicThetaCuspCoefficient_bound j) hp

lemma cubicThetaFunction_continuousAt {p : ℂ × ℝ} (hp : 0 < p.2) :
    ContinuousAt cubicThetaFunction p := by
  have hr : ContinuousAt (fun q : ℂ × ℝ => q.2^(2/3:ℝ)) p :=
    continuousAt_snd.rpow_const (Or.inl (ne_of_gt hp))
  have hc : ContinuousAt (fun q : ℂ × ℝ => ((cubicThetaConstant*q.2^(2/3:ℝ):ℝ):ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (hr.const_mul cubicThetaConstant)
  exact hc.add (cubicThetaAuxiliarySeries_continuousAt 0 hp)

lemma cubicThetaAuxiliarySeries_exponential_bound (j : Fin 3) (z : ℂ)
    {v : ℝ} (hv : 1 ≤ v) :
    ‖cubicThetaAuxiliarySeries j (z,v)‖ ≤ cubicThetaExpConstant 81*Real.exp (-(Real.pi/9)*v) :=
  cubicThetaNonconstant_exponential_bound (by norm_num : (0:ℝ) ≤ 81)
    (cubicThetaCuspCoefficient_bound j) hv z

/-- Each explicitly constructed auxiliary cusp series has an entire
upper-half Mellin transform. -/
theorem cubicThetaAuxiliarySeries_upper_entire (j : Fin 3) (z : ℂ) :
    Differentiable ℂ (mellin (thetaUpper (fun v : ℝ => cubicThetaAuxiliarySeries j (z,v)))) :=
  cubicTheta_upper_mellin_entire (by norm_num : (0:ℝ) ≤ 81)
    (cubicThetaCuspCoefficient_bound j) z

lemma cubicThetaFunction_even (z : ℂ) (v : ℝ) :
    cubicThetaFunction (-z,v) = cubicThetaFunction (z,v) := by
  unfold cubicThetaFunction cubicThetaAuxiliarySeries
  rw [cubicThetaCuspCoefficient_zero,cubicThetaArithmetic_even]

end CubicFirstMoment

end

end OAI
