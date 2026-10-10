import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePoleFactors

namespace OAI

/-! The determinant of the two local prime-free equations has no zeros
on the continued half-plane. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeDeterminant (p : Eisenstein) (s : ℂ) : ℂ :=
  1-(norm p:ℂ)^2*((norm p:ℂ)^(-s))^3

lemma cubicThetaPrimaryPrime_norm_gt_one {p : Eisenstein} (hp : primaryPrime p) :
    1<norm p := by
  have hN := one_le_norm hp.2.ne_zero
  exact lt_of_le_of_ne hN (fun he => hp.2.not_isUnit (isUnit_of_norm_eq_one he.symm))

lemma cubicThetaPrimeDeterminant_analytic {p : Eisenstein} (hp : primaryPrime p) (s : ℂ) :
    AnalyticAt ℂ (cubicThetaPrimeDeterminant p) s :=
  analyticAt_const.sub (analyticAt_const.mul ((cubicThetaPrimeNormPower_analytic hp s).pow 3))

lemma cubicThetaPrimeDeterminant_term {p : Eisenstein} (hp : primaryPrime p) (s : ℂ) :
    (norm p:ℂ)^2*((norm p:ℂ)^(-s))^3=(norm p:ℂ)^(2-3*s) := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [← Complex.cpow_natCast (norm p:ℂ) 2,← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hq]
  congr 1
  ring

theorem cubicThetaPrimeDeterminant_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 1<s.re) : cubicThetaPrimeDeterminant p s≠0 := by
  have ht : ‖(norm p:ℂ)^2*((norm p:ℂ)^(-s))^3‖<1 := by
    rw [cubicThetaPrimeDeterminant_term hp,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hp.2.ne_zero)]
    have he : (2-3*s).re=2-3*s.re := by simp
    rw [he]
    exact Real.rpow_lt_one_of_one_lt_of_neg (cubicThetaPrimaryPrime_norm_gt_one hp) (by linarith)
  intro hz
  have he : (norm p:ℂ)^2*((norm p:ℂ)^(-s))^3=1 :=
    (sub_eq_zero.mp hz).symm
  rw [he,norm_one] at ht
  exact lt_irrefl 1 ht

lemma cubicThetaPrimeDeterminant_pole {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDeterminant p (4/3)=1-((norm p:ℂ)⁻¹)^2 := by
  unfold cubicThetaPrimeDeterminant
  rw [cubicThetaPrimeDeterminant_term hp]
  norm_num only [show (2-3*(4/3):ℂ)=-(2:ℂ) by norm_num]
  rw [Complex.cpow_neg,show (2:ℂ)=((2:ℕ):ℂ) by rfl,Complex.cpow_natCast,inv_pow]

end CubicFirstMoment

end

end OAI
