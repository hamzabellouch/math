import OAI.Probability.SLE.Angle.AngleEigenBounds

namespace OAI

/-! The coefficients needed for the monic three-term recurrence, including
a uniform positive lower bound for its squared-norm ratio. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

lemma angleEigenPolynomial_penultimate (κ : ℝ) (n : ℕ) :
    (angleEigenPolynomial κ (n+1)).coeff n=0 := by
  rw [angleEigenPolynomial_coeff,angleEigenCoefficient,
    ite_eq_right (by omega),dite_eq_left (by omega),
    angleEigenCoefficient_above κ (by omega),mul_zero]

lemma angleEigenPolynomial_second_coeff {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    (angleEigenPolynomial κ (n+2)).coeff n=
      -κ*((n:ℝ)+2)*((n:ℝ)+1)/(4*(κ*((n:ℝ)+1)+4)) := by
  rw [angleEigenPolynomial_coeff,angleEigenCoefficient,
    ite_eq_right (by omega),dite_eq_left (by omega),angleEigenCoefficient_top,mul_one]
  have hd : 4*(κ*((n:ℝ)+1)+4)≠0 := by positivity
  have he : anglePolynomialEigenvalue κ n-anglePolynomialEigenvalue κ (n+2)≠0 :=
    sub_ne_zero.mpr (ne_of_lt (anglePolynomialEigenvalue_strictMono hκ (by omega)))
  apply (div_eq_div_iff he hd).mpr
  unfold anglePolynomialEigenvalue
  push_cast
  ring

def angleRecurrenceCoefficient (κ : ℝ) (n : ℕ) : ℝ :=
  κ*((n:ℝ)+1)*(κ*(n:ℝ)+8)/(4*(κ*((n:ℝ)+1)+4)*(κ*(n:ℝ)+4))

lemma angleRecurrenceCoefficient_zero (κ : ℝ) :
    angleRecurrenceCoefficient κ 0=κ/(2*(κ+4)) := by
  unfold angleRecurrenceCoefficient
  by_cases h : κ+4=0
  · have hk : κ = -4 := by linarith
    subst κ
    norm_num
  · norm_num
    field_simp
    ring

lemma angleRecurrenceCoefficient_sub {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    (angleEigenPolynomial κ (n+2)).coeff n-
      (angleEigenPolynomial κ (n+3)).coeff (n+1)=angleRecurrenceCoefficient κ (n+1) := by
  rw [angleEigenPolynomial_second_coeff hκ,
    show n+3=(n+1)+2 by omega,angleEigenPolynomial_second_coeff hκ]
  unfold angleRecurrenceCoefficient
  push_cast
  have h1 : κ*((n:ℝ)+1)+4≠0 := by positivity
  have h2 : κ*((n:ℝ)+1+1)+4≠0 := by positivity
  field_simp
  ring

lemma angleRecurrenceCoefficient_lower {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    κ/(4*(κ+4))≤angleRecurrenceCoefficient κ n := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hd : 0<4*(κ*((n:ℝ)+1)+4)*(κ*(n:ℝ)+4) := by positivity
  have hc : 0<4*(κ+4) := by positivity
  unfold angleRecurrenceCoefficient
  apply (div_le_div_iff₀ hc hd).mpr
  have hh : 0≤4*κ*(n:ℝ)^2+(4*κ+32)*(n:ℝ)+4*κ+16 := by positivity
  nlinarith [mul_nonneg hκ.le hh]

lemma angleRecurrenceCoefficient_pos {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    0<angleRecurrenceCoefficient κ n :=
  lt_of_lt_of_le (by positivity) (angleRecurrenceCoefficient_lower hκ n)

end SLEExactGauge

end

end OAI
