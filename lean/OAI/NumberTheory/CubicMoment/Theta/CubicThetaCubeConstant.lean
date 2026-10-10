import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitLifting

namespace OAI

/-! The exact arithmetic coefficient of a cube row, with its ramified
factor and finite-ring Euler totient retained. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisenstein_constant_cube_totient {j : Eisenstein} (hj : j≠0)
    (h3 : (3:Eisenstein)∣j^3) :
    cubicThetaEisensteinGaussCoefficient (j^3) 0 =
      (3/2:ℂ)*(normNat j:ℂ)^2*(Nat.card (Residues j)ˣ:ℂ) := by
  rw [cubicThetaEisenstein_constant_units (pow_ne_zero _ hj) ⟨j,rfl⟩,
    cubicTheta_three_units_card (pow_ne_zero _ hj) h3]
  have he := cubicTheta_power_units_card hj 2
  rw [he]
  push_cast
  ring

lemma cubicTheta_cube_row_three_iff {j : Eisenstein} :
    (3:Eisenstein)∣j^3 ↔ lambdaE∣j := by
  constructor
  · intro h
    have hl3 : lambdaE∣(3:Eisenstein) := by
      refine ⟨-lambdaE,?_⟩
      rw [mul_neg,←pow_two,lambdaE_sq]
      ring
    exact lambdaE_prime.dvd_of_dvd_pow (hl3.trans h)
  · rintro ⟨a,rfl⟩
    refine ⟨-lambdaE*a^3,?_⟩
    rw [mul_pow,pow_succ,lambdaE_sq]
    ring

end CubicFirstMoment

end

end OAI
