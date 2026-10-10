import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma scale_against_B {q n r s : ℝ} (hn : 0<n)
    (h : n^2*r ≤ q^4*s) : q^4*r ≤ (q^4/n)^2*s := by
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp
  calc
    _ = q^4*(n^2*r) := by ring
    _ ≤ q^4*(q^4*s) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

theorem normalized_pair_low {q n a χ E : ℝ} (hn : 0<n) (ha : 0≤a) (ha2 : a≤2)
    (hlow : n ≤ q^2*Real.exp (χ/2)) (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (hpower : E*a^200 ≤ 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198) :
    E*a^200 ≤ (q^4/n)^2*Real.exp (2*χ) := by
  have hx : (Real.exp (χ/2))^2=Real.exp χ := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hs : n^2 ≤ q^4*Real.exp χ := by
    have hh := pow_le_pow_left₀ hn.le hlow 2
    rw [mul_pow,hx] at hh
    norm_num only [← pow_mul] at hh
    exact hh
  have hB : q^4 ≤ (q^4/n)^2*Real.exp χ := by
    simpa only [mul_one] using scale_against_B hn (r := 1) (by simpa using hs)
  have he := mul_le_mul hB (pow_le_pow_left₀ ha ha2 198)
    (pow_nonneg ha 198) (by positivity : 0 ≤ (q^4/n)^2*Real.exp χ)
  have hsum : 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198 ≤
      11*2^200*(q^4/n)^2*Real.exp χ := by
    calc
      _ ≤ 9*2^200*(q^4/n)^2*Real.exp χ+8*((q^4/n)^2*Real.exp χ*2^198) := by
        apply add_le_add_right
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤8)
      _ = _ := by ring
  apply (hpower.trans hsum).trans
  calc
    _ ≤ Real.exp χ*(q^4/n)^2*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchi (sq_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add];ring

theorem normalized_pair_small {q n a χ E : ℝ} (hn : 0<n) (ha : 0≤a)
    (hsmall : n*a^99 ≤ q^2) (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (hpower : E*a^200 ≤ 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198) :
    E*a^200 ≤ (q^4/n)^2*Real.exp (2*χ) := by
  have hs : n^2*a^198 ≤ q^4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hn.le (pow_nonneg ha 99)) hsmall 2
    simpa only [mul_pow, ← pow_mul] using hh
  have hB : q^4*a^198 ≤ (q^4/n)^2 := by
    simpa only [mul_one] using scale_against_B hn (s := 1) (by simpa using hs)
  have h1 : 1 ≤ Real.exp χ := by linarith
  have hB' : q^4*a^198 ≤ (q^4/n)^2*Real.exp χ :=
    hB.trans (le_mul_of_one_le_right (sq_nonneg _) h1)
  have hsum : 9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198 ≤
      11*2^200*(q^4/n)^2*Real.exp χ := by
    have hh := mul_le_mul_of_nonneg_left hB' (by norm_num : (0:ℝ)≤8)
    have hc : (8:ℝ) ≤ 2*2^200 := by norm_num
    have ht := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (q^4/n)^2*Real.exp χ)
    nlinarith
  apply (hpower.trans hsum).trans
  calc
    _ ≤ Real.exp χ*(q^4/n)^2*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchi (sq_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add];ring

lemma source_small_overlap {q n a g : ℝ} (ha : 0≤a) (hg : 0≤g)
    (hn : n=q^2*Real.exp g) (hsmall : a≤Real.exp (-g/10)) : n*a^99 ≤ q^2 := by
  have hp := pow_le_pow_left₀ ha hsmall 99
  have he : (Real.exp (-g/10))^99=Real.exp (99*(-g/10)) := by
    rw [←Real.exp_nat_mul]
    norm_num
  rw [he] at hp
  rw [hn]
  calc
    _ ≤ q^2*Real.exp g*Real.exp (99*(-g/10)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = q^2*Real.exp (g+99*(-g/10)) := by rw [mul_assoc,←Real.exp_add]
    _ ≤ q^2*1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith)) (sq_nonneg q)
    _ = _ := mul_one _

end SharpRamseyFive.ScoreScalars

end OAI
