import OAI.NumberTheory.CubicMoment.Angular.AngularHeatLattice

namespace OAI

/-! The angular phase times its radial weight is a harmonic monomial. -/
noncomputable section
namespace CubicFirstMoment

lemma norm_half_nat_rpow (a : Eisenstein) (n : ℕ) :
    (norm a)^((n:ℝ)/2) = ‖(a:ℂ)‖^n := by
  rw [eisenstein_norm_eq_sq,←Real.rpow_natCast ‖a‖ 2,←Real.rpow_mul (_root_.norm_nonneg a)]
  have he : (2:ℝ)*((n:ℝ)/2) = n := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he,Real.rpow_natCast]
  rfl

lemma theta_nat_radial {a : Eisenstein} (ha : a ≠ 0) (n : ℕ) :
    theta (n:ℤ) a*((norm a)^((n:ℝ)/2):ℝ) = (a:ℂ)^n := by
  have haC : (a:ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  have hn : (‖(a:ℂ)‖:ℂ)^n ≠ 0 := pow_ne_zero _
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr haC))
  rw [norm_half_nat_rpow,Complex.ofReal_pow]
  simp only [theta,zpow_natCast,div_pow]
  exact div_mul_cancel₀ _ hn

lemma theta_neg_nat_radial {a : Eisenstein} (ha : a ≠ 0) (n : ℕ) :
    theta (-(n:ℤ)) a*((norm a)^((n:ℝ)/2):ℝ) = (star (a:ℂ))^n := by
  rw [←star_theta ha]
  simpa only [star_mul,Complex.star_def,Complex.conj_ofReal,map_pow,mul_comm] using
    congrArg star (theta_nat_radial ha n)

end CubicFirstMoment

end

end OAI
