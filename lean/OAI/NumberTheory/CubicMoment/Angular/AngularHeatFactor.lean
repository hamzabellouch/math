import OAI.NumberTheory.CubicMoment.Angular.AngularHeatPolynomial
import OAI.NumberTheory.CubicMoment.Estimates.ResidueHarmonicPoisson

namespace OAI

/-! Identification of the normalized angular heat sum with the
polynomial Gaussian sum to which periodic Poisson applies. -/
noncomputable section
namespace CubicFirstMoment

lemma theta_nat_radial_all (a : Eisenstein) (n : ℕ) :
    theta (n:ℤ) a*((norm a)^((n:ℝ)/2):ℝ) = (a:ℂ)^n := by
  by_cases ha : a = 0
  · subst a
    cases n with
    | zero => simp [theta]
    | succ n =>
      simp only [theta,Subalgebra.coe_zero,norm_zero,Complex.ofReal_zero,div_zero,zpow_natCast]
      rw [zero_pow (Nat.succ_ne_zero n),zero_mul]
  · exact theta_nat_radial ha n

lemma theta_neg_nat_radial_all (a : Eisenstein) (n : ℕ) :
    theta (-(n:ℤ)) a*((norm a)^((n:ℝ)/2):ℝ) = (star (a:ℂ))^n := by
  by_cases ha : a = 0
  · subst a
    cases n with
    | zero => simp [theta]
    | succ n =>
      rw [theta_at_zero (by omega),zero_mul]
      simp
  · exact theta_neg_nat_radial ha n

lemma angularHeat_nat_factor (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    angularLatticeHeat q χ (n:ℤ) A ((n:ℝ)/2) t =
      ((t/A)^((n:ℝ)/2):ℝ)*residueHarmonicTheta q χ A n t := by
  unfold angularLatticeHeat residueHarmonicTheta
  rw [←tsum_mul_left]
  apply tsum_congr
  intro z
  have he : norm z*t/A = norm z*(t/A) := by ring
  rw [he,Real.mul_rpow (norm_nonneg z) (div_pos ht hA).le,Complex.ofReal_mul,
    Complex.ofReal_mul]
  calc
    _ = ((t/A)^((n:ℝ)/2):ℝ)*χ (Ideal.Quotient.mk (modulus q) z)*
        (theta (n:ℤ) z*((norm z)^((n:ℝ)/2):ℝ))*
        (Real.exp (-norm z*t/A):ℝ) := by ring
    _ = _ := by rw [theta_nat_radial_all]; ring

lemma angularHeat_neg_nat_factor (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    angularLatticeHeat q χ (-(n:ℤ)) A ((n:ℝ)/2) t =
      ((t/A)^((n:ℝ)/2):ℝ)*residueAntiHarmonicTheta q χ A n t := by
  unfold angularLatticeHeat residueAntiHarmonicTheta
  rw [←tsum_mul_left]
  apply tsum_congr
  intro z
  have he : norm z*t/A = norm z*(t/A) := by ring
  rw [he,Real.mul_rpow (norm_nonneg z) (div_pos ht hA).le,Complex.ofReal_mul,
    Complex.ofReal_mul]
  calc
    _ = ((t/A)^((n:ℝ)/2):ℝ)*χ (Ideal.Quotient.mk (modulus q) z)*
        (theta (-(n:ℤ)) z*((norm z)^((n:ℝ)/2):ℝ))*
        (Real.exp (-norm z*t/A):ℝ) := by ring
    _ = _ := by rw [theta_neg_nat_radial_all]; ring

end CubicFirstMoment

end

end OAI
