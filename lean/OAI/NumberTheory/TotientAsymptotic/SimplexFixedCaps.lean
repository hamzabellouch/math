import OAI.NumberTheory.TotientAsymptotic.SimplexExponential
import OAI.NumberTheory.TotientAsymptotic.ConcentrationExponents

namespace OAI

/-! Fixed-deviation cap estimates with constants uniform in the dimension. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplex_fixed_caps (M K : ℝ) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ M)
    (hS : |(∑ j,w j)-(m:ℝ)| ≤ K) (hQ : (∑ j,(w j)^2) ≤ M*((m:ℝ)+K)) :
    let t := B*((m:ℝ)-1)/(N:ℝ)
    let s := concentrationTilt M
    let E := Real.exp (3*s*(K+1)-(s/100)*((m:ℝ)-1))*(volume (standardSimplex N B)).toReal
    (volume (standardSimplex N B ∩ {v | (∑ j,w j*v j) ≤ (39/40)*t})).toReal ≤ E ∧
    (volume (standardSimplex N B ∩ {v | (41/40)*t ≤ ∑ j,w j*v j})).toReal ≤ E := by
  dsimp only
  let t := B*((m:ℝ)-1)/(N:ℝ)
  let s := concentrationTilt M
  have hs : 0 < s := concentrationTilt_pos hM
  have hsle : s ≤ 1/320 := concentrationTilt_le hM
  have hsm : s*M = 1/320 := concentrationTilt_mul hM
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (m:ℝ) ≤ N := by exact_mod_cast hmN
  have ht : 0 < t := div_pos (mul_pos hB (by linarith)) hn
  have htB : t ≤ B := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hl : 0 ≤ B+s*((39/40)*t) := by positivity
  have hu : 0 ≤ B+s*(-((41/40)*t)) := by
    have hh : s*((41/40)*t) ≤ (1/320)*((41/40)*B) :=
      mul_le_mul hsle (mul_le_mul_of_nonneg_left htB (by norm_num)) (by positivity) (by norm_num)
    nlinarith
  have hwl (j : Fin N) : -(1/2:ℝ) ≤ s*w j := by
    have := mul_nonneg hs.le (hw j).1
    linarith
  have hwu (j : Fin N) : -(1/2:ℝ) ≤ s*(-w j) := by
    have hh := mul_le_mul_of_nonneg_left (hw j).2 hs.le
    rw [hsm] at hh
    nlinarith
  have he := concentration_exponents hM hK (show (1:ℝ) ≤ m by linarith) hS hQ
  have hel : (N:ℝ)*(s*((39/40)*t)/B)-s*(∑ j,w j)+2*s^2*(∑ j,(w j)^2) ≤
      3*s*(K+1)-(s/100)*((m:ℝ)-1) := by
    have hid : (N:ℝ)*(s*((39/40)*t)/B) = s*(39/40)*((m:ℝ)-1) := by
      dsimp [t]
      field_simp
    rw [hid]
    exact he.1
  have heu : (N:ℝ)*(s*(-((41/40)*t))/B)-s*(∑ j,(-w j))+2*s^2*(∑ j,(-w j)^2) ≤
      3*s*(K+1)-(s/100)*((m:ℝ)-1) := by
    have hid : (N:ℝ)*(s*(-((41/40)*t))/B) = -s*(41/40)*((m:ℝ)-1) := by
      dsimp [t]
      field_simp
    rw [hid]
    simp only [Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, neg_sq]
    exact he.2
  constructor
  · exact (volume_simplex_lower_cap_exp N hB ((39/40)*t) s w hs.le hwl hl).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hel) ENNReal.toReal_nonneg)
  · rw [simplex_upper_cap_eq_lower]
    exact (volume_simplex_lower_cap_exp N hB (-((41/40)*t)) s (fun j => -w j) hs.le hwu hu).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr heu) ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
