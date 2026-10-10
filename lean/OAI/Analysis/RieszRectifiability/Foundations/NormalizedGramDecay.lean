import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.GeometricGramRows

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem normalized_mean_zero_gram_decay {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d)
    (ri rj wi wj J A : ℝ) (hri : 0 < ri) (hrj : 0 < rj) (hwi : 0 < wi) (hwj : 0 < wj)
    (hJ : 0 < J) (hA : 0 ≤ A) (hwjSq : wj ^ 2 = rj ^ n)
    (hL : (L : ℝ) ≤ A / (ri * wi)) (hbound : ∀ x, |g x| ≤ A / wj)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z (J * rj)) :
    |∫ x, f x * g x ∂μ| ≤ (G * J ^ (n + 1) * A ^ 2) * (rj / ri) * (wj / wi) := by
  have hraw := mean_zero_gram_bound_of_growth n G μ hgrowth f g hf hg hgI hzero L hLip
    z (J * rj) (A / wj) (mul_pos hJ hrj) (div_nonneg hA hwj.le) hbound hs
  calc
    _ ≤ ((L : ℝ) * (J * rj) * (A / wj)) * (G * (J * rj) ^ n) := hraw
    _ = (L : ℝ) * ((J * rj) * (A / wj) * (G * (J * rj) ^ n)) := by ring
    _ ≤ (A / (ri * wi)) * ((J * rj) * (A / wj) * (G * (J * rj) ^ n)) :=
      mul_le_mul_of_nonneg_right hL (by have hG := hgrowth.1; positivity)
    _ = _ := by
      rw [mul_pow, ← hwjSq, pow_succ]
      field_simp
      ring

theorem normalized_gram_fine_weighted {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d)
    (ri rj wi wj J A : ℝ) (hri : 0 < ri) (hrj : 0 < rj) (hwi : 0 < wi) (hwj : 0 < wj)
    (hJ : 0 < J) (hA : 0 ≤ A) (hwjSq : wj ^ 2 = rj ^ n)
    (hL : (L : ℝ) ≤ A / (ri * wi)) (hbound : ∀ x, |g x| ≤ A / wj)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z (J * rj)) :
    |∫ x, f x * g x ∂μ| * wj ≤ (G * J ^ (n + 1) * A ^ 2) * (rj / ri) * (wj ^ 2 / wi) := by
  have h := mul_le_mul_of_nonneg_right
    (normalized_mean_zero_gram_decay n G μ hgrowth f g hf hg hgI hzero L hLip z
      ri rj wi wj J A hri hrj hwi hwj hJ hA hwjSq hL hbound hs) hwj.le
  convert! h using 1
  ring

theorem normalized_gram_coarse_weighted {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfI : Integrable f μ) (hzero : (∫ x, f x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L g) (z : Ambient d)
    (ri rj wi wj J A : ℝ) (hri : 0 < ri) (hrj : 0 < rj) (hwi : 0 < wi) (hwj : 0 < wj)
    (hJ : 0 < J) (hA : 0 ≤ A) (hwiSq : wi ^ 2 = ri ^ n)
    (hL : (L : ℝ) ≤ A / (rj * wj)) (hbound : ∀ x, |f x| ≤ A / wi)
    (hs : ∀ x, f x ≠ 0 → x ∈ ball z (J * ri)) :
    |∫ x, f x * g x ∂μ| * wj ≤ (G * J ^ (n + 1) * A ^ 2) * (ri / rj) * wi := by
  have h := mul_le_mul_of_nonneg_right
    (normalized_mean_zero_gram_decay n G μ hgrowth g f hg hf hfI hzero L hLip z
      rj ri wj wi J A hrj hri hwj hwi hJ hA hwiSq hL hbound hs) hwj.le
  have heq : (∫ x, g x * f x ∂μ) = ∫ x, f x * g x ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
  rw [heq] at h
  convert! h using 1
  field_simp

theorem nonzero_gram_centers_near {d : ℕ} (μ : Measure (Ambient d))
    (f g : Ambient d → ℝ) (a b : Ambient d) (R S : ℝ)
    (hf : ∀ x, f x ≠ 0 → x ∈ ball a R) (hg : ∀ x, g x ≠ 0 → x ∈ ball b S)
    (hne : (∫ x, f x * g x ∂μ) ≠ 0) : dist a b < R + S := by
  have hnd : ¬ Disjoint (Function.support f) (Function.support g) := by
    intro hd
    exact hne (integral_pairing_zero_of_disjoint_support μ f g hd)
  obtain ⟨x, hxf, hxg⟩ := Set.not_disjoint_iff.mp hnd
  have ha := hf x hxf
  have hb := hg x hxg
  have hax : dist a x < R := by simpa only [mem_ball, dist_comm] using! ha
  exact (dist_triangle a x b).trans_lt (add_lt_add hax hb)

end

end RieszRectifiability

end OAI
