import OAI.Analysis.LipschitzHilbert.Trees.FourGridBandErrors

namespace OAI

/-! The averaging error with arbitrary fixed annular constants. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem complex_band_average_energy (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {r R : ℝ} (hr : 0 < r)
    (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hmesh : δ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      ((8 / (g.meshWidth level * δ)) * (2 * Real.pi * r)⁻¹ ^ 2 +
        8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  obtain ⟨A,hd,hlo,_⟩ := exists_schwartz_band_primitive f hr hlow hhigh
  have hav := g.schwartz_primitive_average_energy A f hd hl hδ hmesh
  have hp := schwartz_primitive_energy A f hr hd hlo
  have hc : 0 ≤ 8 / (g.meshWidth level * δ) :=
    div_nonneg (by norm_num) (mul_pos (g.meshWidth_pos level) hδ).le
  calc
    _ ≤ (8 / (g.meshWidth level * δ)) *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 :=
      hav.trans (add_le_add (mul_le_mul_of_nonneg_left hp hc) le_rfl)
    _ = _ := by ring

theorem general_annular_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {a b D : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hDlow : (2 * Real.pi * b) ^ 2 ≤ D ^ 2)
    (hDhigh : 8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) ≤ D ^ 2)
    (j : ℕ) (hlow : ∀ ξ, |ξ| < a * (4 : ℝ) ^ j → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, b * (4 : ℝ) ^ j < |ξ| → 𝓕 f ξ = 0)
    {level i : ℕ} (hl : level ≤ g.depth)
    (hmesh : g.meshWidth level = ((4 : ℝ) ^ i)⁻¹) :
    (∫ x, ‖bandErrorAt g f level i j x‖ ^ 2 ∂g.lineMeasure) ≤
      D ^ 2 * (1 / 4 : ℝ) ^ Nat.dist i j * ∫ x, ‖f x‖ ^ 2 := by
  have he : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases hji : j < i
  · have h := g.schwartz_low_frequency_error f (mul_nonneg hb (by positivity)) hhigh hl
    simp only [bandErrorAt, ite_eq_left hji]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hmesh, Nat.dist_eq_sub_of_le_right hji.le]
    have hr := four_pow_ratio hji.le
    have hq : 0 ≤ (1 / 4 : ℝ) ^ (i - j) := by positivity
    have hq1 : (1 / 4 : ℝ) ^ (i - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have heq : ((4 : ℝ) ^ i)⁻¹ * (2 * Real.pi * (b * 4 ^ j)) =
        (2 * Real.pi * b) * (1 / 4 : ℝ) ^ (i - j) := by rw [← hr]; ring
    rw [heq, mul_pow]
    have hqq : ((1 / 4 : ℝ) ^ (i - j)) ^ 2 ≤ (1 / 4 : ℝ) ^ (i - j) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hqq (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hDlow hq)
  · have hij : i ≤ j := by omega
    have hδ : 0 < ((4 : ℝ) ^ j)⁻¹ := by positivity
    have hm : ((4 : ℝ) ^ j)⁻¹ ≤ g.meshWidth level := by
      rw [hmesh]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
    have h := complex_band_average_energy g f (mul_pos ha (by positivity)) hlow hhigh hl hδ hm
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, norm_neg]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hmesh, Nat.dist_eq_sub_of_le hij]
    have hr := four_pow_ratio hij
    have heq : (8 / (((4 : ℝ) ^ i)⁻¹ * ((4 : ℝ) ^ j)⁻¹)) *
        (2 * Real.pi * (a * 4 ^ j))⁻¹ ^ 2 +
        8 * ((4 : ℝ) ^ j)⁻¹ / ((4 : ℝ) ^ i)⁻¹ =
        8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) * (1 / 4 : ℝ) ^ (j - i) := by
      rw [← hr]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hDhigh (by positivity)

end LipschitzHilbert

end

end OAI
