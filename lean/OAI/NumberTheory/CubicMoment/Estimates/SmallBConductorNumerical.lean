import OAI.NumberTheory.CubicMoment.Estimates.NoncubeSieveAssembly

namespace OAI

/-! A uniform elementary sieve gap below the exceptional conductor scale.
The root variables isolate the algebra: p=P^(1/3), q=Q^(1/3),
r=N^(1/24). Only one cubic orientation and the ordinary sieve are needed. -/
noncomputable section
namespace CubicFirstMoment

lemma small_conductor_polynomial_min {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hD : p*q^2 ≤ r^6) :
    min (q^3*(p^3+r^24+p^2*r^16)) ((p^3*q^3)^2+r^24) ≤
      r^24+3*r^23*(p*q^2) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hD0 : 0 ≤ p*q^2 := mul_nonneg hp0 (sq_nonneg q)
  have hr12 : r^12 ≤ r^23 := pow_le_pow_right₀ hr (by decide)
  have hr22 : r^22 ≤ r^23 := pow_le_pow_right₀ hr (by decide)
  have hr20 : r^20 ≤ r^23 := pow_le_pow_right₀ hr (by decide)
  rcases le_total (r*q) p with hlarge | hsmall
  · have hq4 : q ≤ q^4 := by
      have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hq (n := 3)) hq0
      nlinarith
    have hpq : p^2*q ≤ r^23 := by
      calc
        _ ≤ p^2*q^4 := mul_le_mul_of_nonneg_left hq4 (sq_nonneg p)
        _ = (p*q^2)^2 := by ring
        _ ≤ (r^6)^2 := pow_le_pow_left₀ hD0 hD 2
        _ = r^12 := by ring
        _ ≤ _ := hr12
    have hfirst : q^3*p^3 ≤ r^23*(p*q^2) := by
      have h := mul_le_mul_of_nonneg_left hpq hD0
      nlinarith
    have hmiddle : q^3*r^24 ≤ r^23*(p*q^2) := by
      have h := mul_le_mul_of_nonneg_left hlarge (mul_nonneg (pow_nonneg hr0 23) (sq_nonneg q))
      nlinarith
    have hpq' : p*q ≤ r^6 := by
      have h := mul_le_mul_of_nonneg_left (show q ≤ q^2 by nlinarith) hp0
      exact h.trans hD
    have hlast : q^3*p^2*r^16 ≤ r^23*(p*q^2) := by
      calc
        _ = (p*q^2)*(p*q)*r^16 := by ring
        _ ≤ (p*q^2)*(r^6)*r^16 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpq' hD0) (pow_nonneg hr0 _)
        _ = (p*q^2)*r^22 := by ring
        _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr22 hD0
    apply (min_le_left _ _).trans
    nlinarith [pow_nonneg hr0 24]
  · have hp3 : p^3 ≤ r^2*(p*q^2) := by
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hsmall 2) hp0
      nlinarith
    have hD3 : (p*q^2)^3 ≤ r^18 := by
      convert pow_le_pow_left₀ hD0 hD 3 using 1
      ring
    have hmain : (p^3*q^3)^2 ≤ r^23*(p*q^2) := by
      calc
        _ = (p*q^2)^3*p^3 := by ring
        _ ≤ (p*q^2)^3*(r^2*(p*q^2)) :=
          mul_le_mul_of_nonneg_left hp3 (pow_nonneg hD0 _)
        _ = (p*q^2)*r^2*(p*q^2)^3 := by ring
        _ ≤ (p*q^2)*r^2*r^18 := mul_le_mul_of_nonneg_left hD3
          (mul_nonneg hD0 (sq_nonneg r))
        _ = (p*q^2)*r^20 := by ring
        _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr20 hD0
    apply (min_le_right _ _).trans
    nlinarith [mul_nonneg (pow_nonneg hr0 23) hD0]

/-- Below conductor N^(3/4), the two relevant sieve bounds have an
absolute gap, apart from the explicit ordinary-sieve diagonal N. -/
lemma small_conductor_sieve_min {P Q N : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hN : 1 ≤ N) (hD : P*Q^2 ≤ N^(3/4:ℝ)) :
    min (Q*(P+N+(P*N)^(2/3:ℝ))) ((P*Q)^2+N) ≤
      N+3*N^(23/24:ℝ)*(P*Q^2)^(1/3:ℝ) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let p := P^(1/3:ℝ)
  let q := Q^(1/3:ℝ)
  let r := N^(1/24:ℝ)
  have hp : 1 ≤ p := Real.one_le_rpow hP (by norm_num)
  have hq : 1 ≤ q := Real.one_le_rpow hQ (by norm_num)
  have hr : 1 ≤ r := Real.one_le_rpow hN (by norm_num)
  have hp3 : p^3 = P := by rw [← Real.rpow_mul_natCast hP0]; norm_num
  have hq3 : q^3 = Q := by rw [← Real.rpow_mul_natCast hQ0]; norm_num
  have hr24 : r^24 = N := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hr6 : r^6 = N^(1/4:ℝ) := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hr16 : r^16 = N^(2/3:ℝ) := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hr23 : r^23 = N^(23/24:ℝ) := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hp2 : p^2 = P^(2/3:ℝ) := by rw [← Real.rpow_mul_natCast hP0]; norm_num
  have hroot : (P*Q^2)^(1/3:ℝ) = p*q^2 := by
    rw [Real.mul_rpow hP0 (sq_nonneg Q),← Real.rpow_pow_comm hQ0]
  have hrootD : p*q^2 ≤ r^6 := by
    rw [← hroot,hr6]
    have h := Real.rpow_le_rpow (mul_nonneg hP0 (sq_nonneg Q)) hD (by norm_num : (0:ℝ) ≤ 1/3)
    rw [← Real.rpow_mul hN0] at h
    norm_num at h
    exact h
  have h := small_conductor_polynomial_min hp hq hr hrootD
  rw [hp3,hq3,hr24,hr16,hr23,hp2,← hroot,← Real.mul_rpow hP0 hN0] at h
  exact h

end CubicFirstMoment

end

end OAI
