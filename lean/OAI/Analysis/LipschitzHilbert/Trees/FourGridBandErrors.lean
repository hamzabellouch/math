import OAI.Analysis.LipschitzHilbert.Fourier.ComplexBandAverage
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights

namespace OAI

/-! Actual radix-four meshes and the geometric error bound for each band. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def fourGrid (origin : ℝ) (depth : ℕ) : FiniteLineGrid where
  branching := 4
  branching_pos := by norm_num
  origin := origin
  width := 1
  width_pos := by norm_num
  depth := depth

theorem fourGrid_mesh (origin : ℝ) (depth i : ℕ) :
    (fourGrid origin depth).meshWidth i = ((4 : ℝ) ^ i)⁻¹ := by
  simp [FiniteLineGrid.meshWidth, fourGrid]

def bandInner (j : ℕ) : ℝ := (4 : ℝ) ^ j / (2 * Real.pi)
def bandOuter (j : ℕ) : ℝ := 2 * (4 : ℝ) ^ j / (2 * Real.pi)

theorem bandInner_pos (j : ℕ) : 0 < bandInner j := by unfold bandInner; positivity

theorem bandInner_scale (j : ℕ) : 2 * Real.pi * bandInner j = (4 : ℝ) ^ j := by
  unfold bandInner
  field_simp

theorem bandOuter_scale (j : ℕ) : 2 * Real.pi * bandOuter j = 2 * (4 : ℝ) ^ j := by
  unfold bandOuter
  field_simp

theorem four_pow_ratio {i j : ℕ} (h : j ≤ i) :
    ((4 : ℝ) ^ i)⁻¹ * (4 : ℝ) ^ j = (1 / 4 : ℝ) ^ (i - j) := by
  have heq : i = j + (i - j) := by omega
  rw [heq, pow_add]
  simp only [Nat.add_sub_cancel_left, one_div, inv_pow]
  field_simp

def bandErrorAt (g : FiniteLineGrid) (f : ℝ → ℂ) (level i j : ℕ) (x : ℝ) : ℂ :=
  (if j < i then f x else 0) - g.scalarAverage g.lineMeasure f level x

def bandError (g : FiniteLineGrid) (f : ℝ → ℂ) (i j : ℕ) : ℝ → ℂ :=
  bandErrorAt g f i i j

theorem geometric_band_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    (j : ℕ) (hlow : ∀ ξ, |ξ| < bandInner j → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, bandOuter j < |ξ| → 𝓕 f ξ = 0)
    {level i : ℕ} (hi : level ≤ g.depth)
    (hmeshwidth : g.meshWidth level = ((4 : ℝ) ^ i)⁻¹) :
    (∫ x, ‖bandErrorAt g f level i j x‖ ^ 2
      ∂g.lineMeasure) ≤
      scaleWeight i j ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have henergy : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases hji : j < i
  · have h := g.schwartz_low_frequency_error f
      (show 0 ≤ bandOuter j by unfold bandOuter; positivity) hhigh hi
    simp only [bandErrorAt, ite_eq_left hji]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ henergy)
    rw [hmeshwidth, bandOuter_scale]
    have hratio := four_pow_ratio hji.le
    have hq : 0 ≤ (1 / 4 : ℝ) ^ (i - j) := by positivity
    have hq1 : (1 / 4 : ℝ) ^ (i - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsq : ((1 / 2 : ℝ) ^ (i - j)) ^ 2 = (1 / 4 : ℝ) ^ (i - j) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hweight : scaleWeight i j ^ 2 = 16 * (1 / 4 : ℝ) ^ (i - j) := by
      simp only [scaleWeight, Nat.dist_eq_sub_of_le_right hji.le, mul_pow, hsq]
      norm_num
    have heq : ((4 : ℝ) ^ i)⁻¹ * (2 * (4 : ℝ) ^ j) =
        2 * (1 / 4 : ℝ) ^ (i - j) := by rw [← hratio]; ring
    rw [hweight, heq]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1)]
  · have hij : i ≤ j := by omega
    have hmesh : (2 * Real.pi * bandInner j)⁻¹ ≤ g.meshWidth level := by
      rw [bandInner_scale, hmeshwidth]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
    have h := g.schwartz_high_frequency_average f
      (bandInner_pos j) hlow hhigh hi hmesh
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, norm_neg]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ henergy)
    rw [hmeshwidth, bandInner_scale]
    have hratio := four_pow_ratio hij
    have hsq : ((1 / 2 : ℝ) ^ (j - i)) ^ 2 = (1 / 4 : ℝ) ^ (j - i) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hweight : scaleWeight i j ^ 2 = 16 * (1 / 4 : ℝ) ^ (j - i) := by
      simp only [scaleWeight, Nat.dist_eq_sub_of_le hij, mul_pow, hsq]
      norm_num
    have heq : 16 * ((4 : ℝ) ^ j)⁻¹ / ((4 : ℝ) ^ i)⁻¹ =
        16 * (1 / 4 : ℝ) ^ (j - i) := by
      rw [← hratio]
      field_simp
    rw [hweight, heq]


theorem fourGrid_band_error (origin : ℝ) (depth : ℕ) (f : SchwartzMap ℝ ℂ)
    (j : ℕ) (hlow : ∀ ξ, |ξ| < bandInner j → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, bandOuter j < |ξ| → 𝓕 f ξ = 0)
    {i : ℕ} (hi : i ≤ depth) :
    (∫ x, ‖bandError (fourGrid origin depth) f i j x‖ ^ 2
      ∂(fourGrid origin depth).lineMeasure) ≤
      scaleWeight i j ^ 2 * ∫ x, ‖f x‖ ^ 2 :=
  geometric_band_error (fourGrid origin depth) f j hlow hhigh hi
    (fourGrid_mesh origin depth i)

end LipschitzHilbert

end

end OAI
