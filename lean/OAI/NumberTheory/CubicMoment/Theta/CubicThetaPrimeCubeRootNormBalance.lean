import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCorrelationFormula

namespace OAI

/-! Exact elimination of the common unit correlation between the zero
and square-frequency projection norms. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_zero_norm_identity {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    (norm p:ℂ)^3*(‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℂ)=
    (‖u‖^2:ℂ)+((norm p:ℂ)^3-(norm p:ℂ)^2)*cubicThetaPrimeCubeRootUnitCorrelation hp u := by
  have he := cubicThetaPrimeCubeRoot_norm_gauss hp 0 u
  rw [map_zero,cubicThetaPrimeCubeRoot_gauss_zero hp,eisenstein_norm_pow,Complex.ofReal_pow,
    star_sub,star_pow,star_pow] at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [he,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 3 hq),one_mul]
  ring

lemma cubicThetaPrimeCubeRoot_square_norm_identity {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (u : cubicThetaAutomorphicL2) :
    (norm p:ℂ)^3*(‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℂ)=
    (‖u‖^2:ℂ)-(norm p:ℂ)^2*cubicThetaPrimeCubeRootUnitCorrelation hp u := by
  have he := cubicThetaPrimeCubeRoot_norm_gauss hp (p^2*h) u
  rw [cubicThetaPrimeCubeRoot_ramanujan hp h hh,eisenstein_norm_pow,Complex.ofReal_pow,
    star_neg,star_pow] at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [he,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 3 hq),one_mul]
  ring

theorem cubicThetaPrimeCubeRoot_norm_balance {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (u : cubicThetaAutomorphicL2) :
    (norm p)^2*‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2+
    ((norm p)^3-(norm p)^2)*‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2=‖u‖^2 := by
  have h0 := cubicThetaPrimeCubeRoot_zero_norm_identity hp u
  have h1 := cubicThetaPrimeCubeRoot_square_norm_identity hp h hh u
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have he : (((norm p)^2*‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2+
    ((norm p)^3-(norm p)^2)*‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℝ):ℂ)=(‖u‖^2:ℂ) := by
    push_cast
    apply mul_left_cancel₀ hq
    linear_combination h0+((norm p:ℂ)-1)*h1
  exact_mod_cast he

end CubicFirstMoment

end

end OAI
