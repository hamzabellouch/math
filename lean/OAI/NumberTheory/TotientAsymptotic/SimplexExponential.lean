import OAI.NumberTheory.TotientAsymptotic.SimplexTilt

namespace OAI

/-! Exponential estimates for linear caps, using only a diagonal volume change. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma log_one_add_quadratic_lower {x : ℝ} (hx : -(1/2 : ℝ) ≤ x) :
    x-2*x^2 ≤ Real.log (1+x) := by
  have hp : 0 < 1+x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  apply le_trans _ hl
  have hm : 0 ≤ x^2*(1+2*x) := mul_nonneg (sq_nonneg x) (by linarith)
  have hid : 1-(1+x)⁻¹ = x/(1+x) := by field_simp; ring
  rw [hid]
  exact (le_div_iff₀ hp).mpr (by nlinarith)

lemma tilted_product_lower (N : ℕ) (w : Fin N → ℝ) (s : ℝ)
    (hw : ∀ i, -(1/2 : ℝ) ≤ s*w i) :
    Real.exp (s*(∑ i, w i)-2*s^2*(∑ i, (w i)^2)) ≤
      ∏ i, (1+s*w i) := by
  have he : s*(∑ i, w i)-2*s^2*(∑ i, (w i)^2) =
      ∑ i, (s*w i-2*(s*w i)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le)
  intro i _
  have hp : 0 < 1+s*w i := by have := hw i; linarith
  exact (Real.exp_le_exp.mpr (log_one_add_quadratic_lower (hw i))).trans_eq (Real.exp_log hp)

lemma simplex_tilt_power (N : ℕ) {B : ℝ} (hB : 0 < B) (s t : ℝ)
    (hT : 0 ≤ B+s*t) :
    (B+s*t)^N ≤ B^N*Real.exp ((N:ℝ)*(s*t/B)) := by
  have hbase : B+s*t ≤ B*Real.exp (s*t/B) := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s*t/B)) hB.le
    convert hh using 1
    field_simp [hB.ne']
    ring
  calc
    _ ≤ (B*Real.exp (s*t/B))^N := pow_le_pow_left₀ hT hbase N
    _ = _ := by rw [mul_pow, Real.exp_nat_mul]

/-- An explicit Chernoff estimate for the lower cap of a uniform simplex. -/
theorem volume_simplex_lower_cap_exp (N : ℕ) {B : ℝ} (hB : 0 < B)
    (t s : ℝ) (w : Fin N → ℝ) (hs : 0 ≤ s)
    (hw : ∀ i, -(1/2 : ℝ) ≤ s*w i) (hT : 0 ≤ B+s*t) :
    (volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t})).toReal ≤
      Real.exp ((N:ℝ)*(s*t/B)-s*(∑ i, w i)+2*s^2*(∑ i, (w i)^2))*
        (volume (standardSimplex N B)).toReal := by
  have hp : ∀ i, 0 < 1+s*w i := fun i => by have := hw i; linarith
  have hprod := tilted_product_lower N w s hw
  have hpow := simplex_tilt_power N hB s t hT
  have hfac : 0 < (N.factorial:ℝ) := by positivity
  have hden : 0 < (N.factorial:ℝ)*Real.exp (s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2)) := by positivity
  apply (volume_simplex_lower_cap_le N B t s w hs hp hT).trans
  calc
    _ ≤ (B^N*Real.exp ((N:ℝ)*(s*t/B)))/
        ((N.factorial:ℝ)*Real.exp (s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2))) := by
      apply div_le_div₀ (by positivity) hpow hden
      exact mul_le_mul_of_nonneg_left hprod hfac.le
    _ = _ := by
      rw [volume_standardSimplex N hB.le, ENNReal.toReal_ofReal (by positivity)]
      conv_rhs => rw [show (N:ℝ)*(s*t/B)-s*(∑ i,w i)+2*s^2*(∑ i,(w i)^2) =
        (N:ℝ)*(s*t/B)-(s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2)) by ring, Real.exp_sub]
      ring

end TotientAsymptotic

end

end OAI
