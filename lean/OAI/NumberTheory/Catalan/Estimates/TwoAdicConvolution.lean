import OAI.NumberTheory.Catalan.Polynomial.TwoAdicCoefficients

namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

theorem two_pow_sub_dvd_coeff_mul (P Q : ℤ[X]) (B i : ℕ)
    (hQ : ∀ j, (2 : ℤ) ^ (B - j) ∣ Q.coeff j) :
    (2 : ℤ) ^ (B - i) ∣ (P * Q).coeff i := by
  rw [coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨a, b⟩ hab
  have hab' : a + b = i := Finset.mem_antidiagonal.mp hab
  have hpow : (2 : ℤ) ^ (B - i) ∣ (2 : ℤ) ^ (B - b) :=
    pow_dvd_pow 2 (by omega)
  exact dvd_mul_of_dvd_right (hpow.trans (hQ b)) (P.coeff a)

theorem rowP_coeff_two_pow_dvd (N r i : ℕ) :
    (2 : ℤ) ^ (Cdegree N - 2 - i) ∣ (rowP N r).coeff i := by
  unfold rowP
  apply two_pow_sub_dvd_coeff_mul
  intro j
  have he : Cdegree N - 2 - j = Cdegree N - 1 - j - 1 := by omega
  rw [he]
  exact reversed_T_coeff_two_pow_dvd (Cdegree N) (rowDistance N r : ℤ) j

theorem rowD_coeff_two_pow_dvd (N r i : ℕ) :
    (2 : ℤ) ^ (Cdegree N - 1 - i) ∣ (rowD N r).coeff i := by
  unfold rowD
  rw [mul_assoc, mul_left_comm]
  apply two_pow_sub_dvd_coeff_mul
  intro j
  exact signed_reversed_U_coeff_two_pow_dvd (Cdegree N)
    (Int.sign (rowOffset N r)) ((rowDistance N r : ℤ) - 1) j

end InternalCatalan

end

end OAI
