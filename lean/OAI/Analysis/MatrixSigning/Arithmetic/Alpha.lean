import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ScalarPsi

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

lemma psi_even (x : ℝ) : psi (-x) = psi x := by simp [psi]
lemma psi₁_odd (x : ℝ) : psi₁ (-x) = -psi₁ x := by simp [psi₁,psi_even]; ring
lemma kappa_even (x : ℝ) : kappa (-x) = kappa x := by simp [kappa,psi_even]

lemma psi_ge_base {x : ℝ} (hx : |x| < 1) : 1-x^2 ≤ psi x := by
  have hp := psi_pos hx
  have hle := psi_le_one hx
  have hc := psi_cube hx
  have hs : psi x ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hs)]

lemma abs_derivative_ratio {x : ℝ} (hx : |x| < 1) :
    |psi₁ x| / (psi x * kappa x) = 3 * |x| * psi x^2/(3+x^2) := by
  have hw := psi_pos hx
  have hw0 := ne_of_gt hw
  have hx3 : 3+x^2 ≠ 0 := by positivity
  rw [psi₁,abs_div,abs_mul]
  simp only [abs_mul,abs_of_nonneg (sq_nonneg (psi x))]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  unfold kappa
  field_simp
  ring

lemma abs_derivative_ratio_le {x : ℝ} (hx : |x| < 1) :
    |psi₁ x| / (psi x * kappa x) ≤ 1 := by
  rw [abs_derivative_ratio hx]
  apply (div_le_one (by positivity : 0 < 3+x^2)).mpr
  have hp := psi_pos hx
  have hle := psi_le_one hx
  have hs : psi x^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul hs hx.le (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [sq_nonneg x]

lemma weighted_kappa_lower {x : ℝ} (hx : |x| < 1) :
    2/(3*(1-x^2)) ≤ psi x * kappa x := by
  have hp := psi_pos hx
  have h0 := ne_of_gt hp
  have hle := psi_le_one hx
  have hc := psi_cube hx
  rw [← hc]
  unfold kappa
  apply (div_le_iff₀ (by positivity : 0 < 3*psi x^3)).mpr
  field_simp
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (pow_nonneg hp.le 3)]

def alpha (x _A B : ℝ) : ℝ := 1 - 2*x*B/(3*(1-x^2))
def beta (x A _B : ℝ) : ℝ := 1 + 2*x*A/(3*(1-x^2))

lemma alpha_neg (x A B : ℝ) : alpha (-x) B A = beta x A B := by
  simp [alpha,beta]; ring
lemma beta_neg (x A B : ℝ) : beta (-x) B A = alpha x A B := by
  simp [alpha,beta]; ring

lemma coefficient_bounds_nonneg {x A B : ℝ} (hx : |x| < 1) (hx0 : 0 ≤ x)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    (2/3 : ℝ) ≤ alpha x A B ∧ alpha x A B ≤ 1 ∧
    1 ≤ beta x A B ∧ beta x A B ≤ 2/(1-x^2) ∧
    beta x A B * (1-x) ≤ 1+x := by
  have hr := base_pos hx
  have xp := (abs_lt.mp hx).2
  have hden : 0 < 3*(1-x^2) := by positivity
  have hmx : 0 ≤ 1-x := by linarith
  have hm := mul_le_mul_of_nonneg_left hBl.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)
  have hmA := mul_le_mul_of_nonneg_left hAl.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)
  have hl : 2*x*B/(3*(1-x^2)) ≤ (1/3 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (1-x)]
  have hpB : 0 ≤ 2*x*B/(3*(1-x^2)) := by positivity
  have hpA : 0 ≤ 2*x*A/(3*(1-x^2)) := by positivity
  refine ⟨by unfold alpha; linarith, by unfold alpha; linarith,
    by unfold beta; linarith, ?_, ?_⟩
  · unfold beta
    apply (le_div_iff₀ hr).mpr
    field_simp
    nlinarith [sq_nonneg x]
  · have he : beta x A B * (1-x) =
        ((3*(1-x^2)+2*x*A)*(1-x))/(3*(1-x^2)) := by
      unfold beta
      field_simp
    rw [he]
    apply (div_le_iff₀ hden).mpr
    have hmA' := mul_le_mul_of_nonneg_right hmA hmx
    nlinarith [mul_nonneg hx0 hr.le]

lemma product_bounds {x A B : ℝ} (hx : |x| < 1)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    (2/3 : ℝ) ≤ alpha x A B * beta x A B ∧
    alpha x A B * beta x A B ≤ 2/(1-x^2) ∧
    0 < alpha x A B ∧ 0 < beta x A B := by
  have nonneg_case : ∀ y C D : ℝ, |y| < 1 → 0 ≤ y → 0 < C → 0 < D →
      C < 1+y → D < 1-y →
      (2/3 : ℝ) ≤ alpha y C D * beta y C D ∧
      alpha y C D * beta y C D ≤ 2/(1-y^2) ∧
      0 < alpha y C D ∧ 0 < beta y C D := by
    intro y C D hy hy0 hC hD hCl hDl
    obtain ⟨ha,ha',hb,hb',_⟩ := coefficient_bounds_nonneg hy hy0 hC hD hCl hDl
    have hap : 0 < alpha y C D := by linarith
    have hbp : 0 < beta y C D := by linarith
    refine ⟨?_,?_,hap,hbp⟩
    · nlinarith [mul_nonneg hap.le (sub_nonneg.mpr hb)]
    · nlinarith [mul_nonneg hbp.le (sub_nonneg.mpr ha')]
  by_cases hx0 : 0 ≤ x
  · exact nonneg_case x A B hx hx0 hA hB hAl hBl
  · have hh := nonneg_case (-x) B A (by simpa) (by linarith) hB hA
      (by linarith) (by linarith)
    simpa only [alpha_neg,beta_neg,neg_sq,mul_comm,and_assoc,and_comm,and_left_comm] using hh

lemma kappa_product_bounds {x A B : ℝ} (hx : |x| < 1)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    (1/3 : ℝ) ≤ kappa x / (alpha x A B * beta x A B) ∧
    (1/3 : ℝ) ≤ psi x * kappa x / (alpha x A B * beta x A B) ∧
    psi x / (alpha x A B * beta x A B) ≤ (3/2 : ℝ) := by
  obtain ⟨hl,hu,ha,hb⟩ := product_bounds hx hA hB hAl hBl
  have hp := psi_pos hx
  have hp1 := psi_le_one hx
  have hk := kappa_pos hx
  have hr := base_pos hx
  have hw := weighted_kappa_lower hx
  have hq : alpha x A B * beta x A B ≤ 3 * (psi x * kappa x) := by
    have he : 2/(1-x^2) = 3*(2/(3*(1-x^2))) := by field_simp
    rw [he] at hu
    linarith
  have hprod := mul_pos ha hb
  refine ⟨(le_div_iff₀ hprod).mpr ?_, (le_div_iff₀ hprod).mpr ?_,
    (div_le_iff₀ hprod).mpr ?_⟩
  · nlinarith [mul_le_of_le_one_left hk.le hp1]
  · nlinarith
  · nlinarith

lemma light_squares_nonneg {x A B : ℝ} (hx : |x| < 1) (hx0 : 0 ≤ x)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    alpha x A B * A^2 ≤ 3 * beta x A B * psi x ∧
    beta x A B * B^2 ≤ 3 * alpha x A B * psi x := by
  obtain ⟨ha,ha',hb,_,hb'⟩ := coefficient_bounds_nonneg hx hx0 hA hB hAl hBl
  have hp := psi_pos hx
  have hpr := psi_ge_base hx
  have hr := base_pos hx
  have hm : 0 < 1-x := by have h := (abs_lt.mp hx).2; linarith
  have hA2 : A^2 ≤ 1-x^2+2*x*A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAl.le) (by linarith : 0 ≤ A+1-x)]
  have hEq : 3*(1-x^2)*beta x A B = 3*(1-x^2)+2*x*A := by
    unfold beta
    field_simp
  have hAs : A^2 ≤ 3*beta x A B*psi x := by
    have hmul := mul_le_mul_of_nonneg_left hpr (by linarith : 0 ≤ 3*beta x A B)
    nlinarith
  have hBs : beta x A B * B^2 ≤ 1-x^2 := by
    have hbpos : 0 ≤ beta x A B := by linarith
    have hsq : B^2 ≤ (1-x)^2 := by nlinarith
    have hv := mul_le_mul_of_nonneg_left hsq hbpos
    have hw := mul_le_mul_of_nonneg_right hb' hm.le
    nlinarith
  constructor
  · nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr ha')]
  · nlinarith [mul_nonneg hp.le (sub_nonneg.mpr ha)]

lemma light_squares {x A B : ℝ} (hx : |x| < 1)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    alpha x A B * A^2 ≤ 3 * beta x A B * psi x ∧
    beta x A B * B^2 ≤ 3 * alpha x A B * psi x := by
  by_cases hx0 : 0 ≤ x
  · exact light_squares_nonneg hx hx0 hA hB hAl hBl
  · have hh := light_squares_nonneg (x := -x) (A := B) (B := A)
      (by simpa) (by linarith) hB hA (by linarith) (by linarith)
    simpa only [alpha_neg,beta_neg,psi_even,and_comm] using hh

end
end CurrentKS.Scalar

end OAI
