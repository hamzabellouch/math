import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma q_le_B {q n : ℝ} (hq : 0<q) (hn : 0<n) (hcap : n≤q^3) :
    q ≤ q^4/n := by
  apply (le_div_iff₀ hn).mpr
  calc q*n ≤ q*q^3 := mul_le_mul_of_nonneg_left hcap hq.le
       _ = q^4 := by ring

lemma qsq_le_Bexp {q n χ : ℝ} (hn : 0<n)
    (hlow : n ≤ q^2*Real.exp χ) : q^2 ≤ q^4/n*Real.exp χ := by
  apply (mul_le_mul_iff_left₀ hn).mp
  calc
    _ ≤ q^2*(q^2*Real.exp χ) := mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
    _ = _ := by field_simp

theorem normalized_degree_low {q n a χ D : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0≤a) (ha2 : a≤2) (hcap : n≤q^3) (hlow : n≤q^2*Real.exp χ)
    (hexp : (10*2^200:ℝ)≤Real.exp χ)
    (hpower : D*a^200 ≤ 12*q^2*a^199+16*q*a^198) :
    D*a^200 ≤ (q^4/n)*Real.exp (2*χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hB : 0≤q^4/n := by positivity
  have h1 : 1≤Real.exp χ := by linarith
  have hbexp := le_mul_of_one_le_right hB h1
  have hqexp := (q_le_B hq0 hn hcap).trans hbexp
  have hi := mul_le_mul (qsq_le_Bexp hn hlow) (pow_le_pow_left₀ ha ha2 199)
    (pow_nonneg ha 199) (by positivity : 0≤q^4/n*Real.exp χ)
  have hj := mul_le_mul hqexp (pow_le_pow_left₀ ha ha2 198)
    (pow_nonneg ha 198) (by positivity : 0≤q^4/n*Real.exp χ)
  apply hpower.trans
  calc
    _ = 12*(q^2*a^199)+16*(q*a^198) := by ring
    _ ≤ 12*(q^4/n*Real.exp χ*2^199)+16*(q^4/n*Real.exp χ*2^198) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num))
        (mul_le_mul_of_nonneg_left hj (by norm_num))
    _ = 10*2^200*(q^4/n)*Real.exp χ := by ring
    _ ≤ Real.exp χ*(q^4/n)*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hB) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add]; ring

theorem normalized_degree_small {q n a χ D C : ℝ} (hq : 0<q) (hn : 0<n)
    (ha : 0≤a) (ha2 : a≤2) (hcap : n≤q^3) (hsmall : n*a≤C*q^2)
    (hexp : (12*C+16)*2^198≤Real.exp (2*χ))
    (hpower : D*a^200 ≤ 12*q^2*a^199+16*q*a^198) :
    D*a^200 ≤ (q^4/n)*Real.exp (2*χ) := by
  have hqa : q^2*a≤C*(q^4/n) := by
    apply (mul_le_mul_iff_left₀ hn).mp
    calc
      _ = q^2*(n*a) := by ring
      _ ≤ q^2*(C*q^2) := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = _ := by field_simp
  have hfirst : q^2*a^199≤C*(q^4/n)*a^198 := by
    calc _ = (q^2*a)*a^198 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hqa (pow_nonneg ha 198)
  have hsecond := mul_le_mul_of_nonneg_right (q_le_B hq hn hcap) (pow_nonneg ha 198)
  have hC : 0≤C := by
    have := mul_nonneg hn.le ha
    nlinarith [sq_pos_of_pos hq]
  apply hpower.trans
  calc
    _ = 12*(q^2*a^199)+16*(q*a^198) := by ring
    _ ≤ 12*(C*(q^4/n)*a^198)+16*(q^4/n*a^198) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = (q^4/n)*((12*C+16)*a^198) := by ring
    _ ≤ (q^4/n)*((12*C+16)*2^198) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha ha2 198) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

theorem normalized_degree_truncated {q n a χ D : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0≤a) (ha2 : a≤2) (hcap : n≤q^3)
    (hexp : (16*2^198:ℝ)≤Real.exp (2*χ))
    (hpower : D*a^2≤8*(q+1)) : D*a^200≤(q^4/n)*Real.exp (2*χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hh := mul_le_mul_of_nonneg_right hpower (pow_nonneg ha 198)
  have he : D*a^2*a^198=D*a^200 := by ring
  rw [he] at hh
  apply hh.trans
  calc
    _ ≤ 16*q*a^198 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha 198)
      linarith
    _ ≤ 16*(q^4/n)*2^198 := mul_le_mul
      (mul_le_mul_of_nonneg_left (q_le_B hq0 hn hcap) (by norm_num))
      (pow_le_pow_left₀ ha ha2 198) (pow_nonneg ha 198) (by positivity)
    _ = (q^4/n)*(16*2^198) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

end SharpRamseyFive.ScoreScalars

end OAI
