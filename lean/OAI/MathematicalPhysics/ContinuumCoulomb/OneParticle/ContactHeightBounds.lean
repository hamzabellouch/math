import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactAdjustment

namespace OAI

/-! Uniform direct and inverse moduli for the nine-link height solve. The
four sloping links keep this one-dimensional solve quantitatively regular. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactHeight_interval_bounds {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) :
    2 / 5 ≤ h ∧ h ≤ 3 / 4 := by
  have hl0 : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hu0 : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  have hl := contactHeightLow_sq hc hc'
  have hu := contactHeightHigh_sq hc hc'
  constructor
  · nlinarith [hh.1]
  · nlinarith [hh.2]

theorem adjustedContactForward_slope {length h₁ h₂ : ℝ}
    (hl : 99 / 100 ≤ length) (hl' : length ≤ 101 / 100)
    (hh₁ : 2 / 5 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 3 / 4) :
    (h₂ - h₁) / 5 ≤ adjustedContactForward length h₁ - adjustedContactForward length h₂ ∧
      adjustedContactForward length h₁ - adjustedContactForward length h₂ ≤ 2 * (h₂ - h₁) := by
  have h₁0 : 0 ≤ h₁ := by linarith
  have h₂0 : 0 ≤ h₂ := by linarith
  have h₁U : h₁ ≤ 3 / 4 := hh.trans hh₂
  have h₂L : 2 / 5 ≤ h₂ := hh₁.trans hh
  have hl0 : 0 ≤ length := by linarith
  have hl2lo : (99 / 100 : ℝ) ^ 2 ≤ length ^ 2 := by nlinarith
  have hl2hi : length ^ 2 ≤ (101 / 100 : ℝ) ^ 2 := by nlinarith
  have hr₁ : 0 ≤ length ^ 2 - h₁ ^ 2 := by nlinarith
  have hr₂ : 0 ≤ length ^ 2 - h₂ ^ 2 := by nlinarith
  let x₁ := adjustedContactForward length h₁
  let x₂ := adjustedContactForward length h₂
  have hx₁ : 0 ≤ x₁ := Real.sqrt_nonneg _
  have hx₂ : 0 ≤ x₂ := Real.sqrt_nonneg _
  have hx₁sq : x₁ ^ 2 = length ^ 2 - h₁ ^ 2 := Real.sq_sqrt hr₁
  have hx₂sq : x₂ ^ 2 = length ^ 2 - h₂ ^ 2 := Real.sq_sqrt hr₂
  have hx₁lo : 1 / 2 ≤ x₁ := by nlinarith
  have hx₂lo : 1 / 2 ≤ x₂ := by nlinarith
  have hx₁hi : x₁ ≤ 2 := by nlinarith
  have hx₂hi : x₂ ≤ 2 := by nlinarith
  have hxx : x₂ ≤ x₁ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (add_nonneg h₁0 h₂0)]
  have hid : (x₁ - x₂) * (x₁ + x₂) = (h₂ - h₁) * (h₁ + h₂) := by nlinarith
  change (h₂ - h₁) / 5 ≤ x₁ - x₂ ∧ x₁ - x₂ ≤ 2 * (h₂ - h₁)
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxx)
      (show 0 ≤ 4 - (x₁ + x₂) by linarith),
      mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ h₁ + h₂ - 4 / 5 by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxx)
      (show 0 ≤ x₁ + x₂ - 1 by linarith),
      mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 2 - (h₁ + h₂) by linarith)]

theorem adjustedContactSpan_broad_slope {h₁ h₂ : ℝ}
    (hh₁ : 2 / 5 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 3 / 4)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    (h₂ - h₁) / 2 ≤ adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ∧
      adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ≤ 8 * (h₂ - h₁) := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_slope
    (show 99 / 100 ≤ lengths k by have := hl k hk; norm_num [contactLengthTolerance] at this ⊢; linarith)
    (show lengths k ≤ 101 / 100 by have := hl' k hk; norm_num [contactLengthTolerance] at this ⊢; linarith)
    hh₁ hh hh₂
  have hf₂ := hf 2 (by norm_num)
  have hf₃ := hf 3 (by norm_num)
  have hf₅ := hf 5 (by norm_num)
  have hf₆ := hf 6 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  constructor <;> linarith [hf₂.1, hf₂.2, hf₃.1, hf₃.2, hf₅.1, hf₅.2, hf₆.1, hf₆.2]

theorem adjustedContactSpan_slope {c h₁ h₂ : ℝ}
    (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh₁ : h₁ ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (hh₂ : h₂ ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) (hh : h₁ ≤ h₂)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    (h₂ - h₁) / 2 ≤ adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ∧
      adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ≤ 8 * (h₂ - h₁) :=
  adjustedContactSpan_broad_slope (contactHeight_interval_bounds hc hc' hh₁).1 hh
    (contactHeight_interval_bounds hc hc' hh₂).2 lengths hl hl'

theorem adjustedContactSpan_broad_inverse_error {h h₀ span : ℝ}
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4))
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hroot : adjustedContactSpan lengths h₀ = span) :
    |h - h₀| ≤ 2 * |adjustedContactSpan lengths h - span| := by
  rcases le_total h h₀ with hle | hle
  · have hs := (adjustedContactSpan_broad_slope hh.1 hle hh₀.2 lengths hl hl').1
    rw [hroot] at hs
    have hx : 0 ≤ adjustedContactSpan lengths h - span := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonneg hx]
    linarith
  · have hs := (adjustedContactSpan_broad_slope hh₀.1 hle hh.2 lengths hl hl').1
    rw [hroot] at hs
    have hx : adjustedContactSpan lengths h - span ≤ 0 := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonpos hx]
    linarith

theorem adjustedContactSpan_inverse_error {c h h₀ span : ℝ}
    (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (hh₀ : h₀ ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hroot : adjustedContactSpan lengths h₀ = span) :
    |h - h₀| ≤ 2 * |adjustedContactSpan lengths h - span| :=
  adjustedContactSpan_broad_inverse_error (contactHeight_interval_bounds hc hc' hh)
    (contactHeight_interval_bounds hc hc' hh₀) lengths hl hl' hroot

theorem adjustedContactSpan_broad_lipschitz {h h' : ℝ}
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4)) (hh' : h' ∈ Set.Icc (2 / 5) (3 / 4))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    |adjustedContactSpan lengths h - adjustedContactSpan lengths h'| ≤ 8 * |h - h'| := by
  rcases le_total h h' with hle | hle
  · obtain ⟨hlower, hupper⟩ := adjustedContactSpan_broad_slope hh.1 hle hh'.2 lengths hl hl'
    have hs : 0 ≤ adjustedContactSpan lengths h - adjustedContactSpan lengths h' := by linarith
    rw [abs_of_nonneg hs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · obtain ⟨hlower, hupper⟩ := adjustedContactSpan_broad_slope hh'.1 hle hh.2 lengths hl hl'
    have hs : adjustedContactSpan lengths h - adjustedContactSpan lengths h' ≤ 0 := by linarith
    rw [abs_of_nonpos hs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

end ContinuumCoulomb

end

end OAI
