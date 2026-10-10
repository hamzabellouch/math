import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalTower
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularMellin

namespace OAI

/-! The actual automorphic arithmetic theta section generates every
nonzero angular series by its horizontal derivatives. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaArithmeticHorizontalSlice (v : ℝ) (hv : 0<v) : ℂ → ℂ :=
  fun z => cubicThetaNormalizedSeriesSection.val ⟨(z,v),hv⟩

lemma cubicThetaArithmeticHorizontalSlice_eq (v : ℝ) (hv : 0<v) :
    cubicThetaArithmeticHorizontalSlice v hv=fun z =>
      cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) := by
  funext z
  exact cubicThetaNormalizedSeriesSection_apply ⟨(z,v),hv⟩

theorem cubicThetaArithmetic_positive_tower (v : ℝ) (hv : 0<v) {k : ℕ} (hk : 0<k) :
    (cubicThetaWirtingerPositive^[k]) (cubicThetaArithmeticHorizontalSlice v hv)=
      fun z => cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (k:ℤ)) (z,v) := by
  rw [cubicThetaArithmeticHorizontalSlice_eq]
  exact cubicThetaWirtingerPositive_iterate_const (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound hv _ hk

theorem cubicThetaArithmetic_negative_tower (v : ℝ) (hv : 0<v) {k : ℕ} (hk : 0<k) :
    (cubicThetaWirtingerNegative^[k]) (cubicThetaArithmeticHorizontalSlice v hv)=
      fun z => cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (-(k:ℤ))) (z,v) := by
  rw [cubicThetaArithmeticHorizontalSlice_eq]
  exact cubicThetaWirtingerNegative_iterate_const (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound hv _ hk

/-- Extend the actual derivative on the positive vertical axis by zero.
Only positive heights enter its Mellin transform. -/
def cubicThetaArithmeticAngularAxis (ℓ : ℤ) (v : ℝ) : ℂ :=
  if hv : 0<v then
    if 0≤ℓ then (cubicThetaWirtingerPositive^[ℓ.natAbs]) (cubicThetaArithmeticHorizontalSlice v hv) 0
    else (cubicThetaWirtingerNegative^[ℓ.natAbs]) (cubicThetaArithmeticHorizontalSlice v hv) 0
  else 0

theorem cubicThetaArithmeticAngularAxis_eq {ℓ : ℤ} (hℓ : ℓ≠0) {v : ℝ} (hv : 0<v) :
    cubicThetaArithmeticAngularAxis ℓ v=
      cubicThetaNonconstant (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient ℓ) (0,v) := by
  have hk : 0<ℓ.natAbs := Int.natAbs_pos.mpr hℓ
  unfold cubicThetaArithmeticAngularAxis
  rw [dite_eq_left hv]
  by_cases hpos : 0≤ℓ
  · have he : (ℓ.natAbs:ℤ)=ℓ := by omega
    rw [ite_eq_left hpos,cubicThetaArithmetic_positive_tower v hv hk,he]
  · rw [ite_eq_right hpos,cubicThetaArithmetic_negative_tower v hv hk]
    have he : -(ℓ.natAbs:ℤ)=ℓ := by omega
    rw [he]

theorem cubicThetaArithmeticAngularAxis_completed {ℓ : ℤ} (hℓ : ℓ≠0)
    {s : ℂ} (hs : 3/2<s.re) :
    mellin (cubicThetaArithmeticAngularAxis ℓ) (2*s+(ℓ.natAbs:ℂ)-1)=
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
        Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
        cubicThetaDirichlet (fun n => theta ℓ n*cubicThetaArithmeticCoefficient n) (2*s-1) := by
  calc
    _ = mellin (fun v => cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient ℓ) (0,v))
        (2*s+(ℓ.natAbs:ℂ)-1) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaArithmeticAngularAxis_eq hℓ hv]
    _ = _ := cubicThetaAngular_completed (by norm_num : (0:ℝ)≤81)
      cubicThetaArithmeticCoefficient_norm_le ℓ hs

end CubicFirstMoment

end

end OAI
