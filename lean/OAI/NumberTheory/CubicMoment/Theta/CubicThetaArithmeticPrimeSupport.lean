import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! The explicit theta model has no unramified prime of valuation two.
This is a property of its literal arithmetic formula, separate from the
still required identification with the analytic residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaCoordinates_not_square {p n : Eisenstein}
    (hp : primaryPrime p) (hn : ¬p ∣ n) :
    ¬Nonempty (CubicThetaCoordinates (p^2*n)) := by
  rintro ⟨R⟩
  have hd : ¬p ∣ R.cubePart := by
    intro hd
    have hp3 : p^3 ∣ p^2*n := by
      rw [R.numerator_eq]
      exact (pow_dvd_pow_of_dvd hd 3).trans (dvd_mul_left (R.cubePart^3)
        ((R.unit:Eisenstein)*lambdaE^R.order*R.squarefreePart)) |>.trans
          (by apply dvd_of_eq; ring)
    rw [show (3:ℕ)=2+1 by omega,pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hp.2.ne_zero)] at hp3
    exact hn hp3
  have hpu : IsCoprime p (R.unit:Eisenstein) := by
    exact hp.2.coprime_iff_not_dvd.mpr
      (fun hd => hp.2.not_isUnit (isUnit_of_dvd_unit hd R.unit.isUnit))
  have hpl : IsCoprime p (lambdaE^R.order) := (primary_coprime_lambda hp.1).pow_right
  have hpd : IsCoprime p (R.cubePart^3) :=
    (hp.2.coprime_iff_not_dvd.mpr hd).pow_right
  have hc : p^2 ∣ R.squarefreePart := by
    have he : p^2 ∣ ((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart := by
      have heq : p^2*n=((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
        R.numerator_eq.trans (by ring)
      exact (dvd_mul_right (p^2) n).trans (dvd_of_eq heq)
    exact ((hpu.mul_right hpl).mul_right hpd).pow_left.dvd_of_dvd_mul_left he
  exact hp.2.not_isUnit (R.squarefree p (by simpa only [pow_two] using hc))

theorem cubicThetaArithmeticCoefficient_prime_square {p n : Eisenstein}
    (hp : primaryPrime p) (hn : ¬p ∣ n) :
    cubicThetaArithmeticCoefficient (p^2*n)=0 := by
  rw [cubicThetaArithmeticCoefficient,dite_eq_right (cubicThetaCoordinates_not_square hp hn)]

end CubicFirstMoment

end

end OAI
