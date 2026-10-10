import OAI.NumberTheory.Ostmann.Characters.CharacterHorizontalGrowth
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourResidue
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothMellinBounds

namespace OAI

/-! # Fifth-order decay of the actual horizontal contour integrals -/

namespace Ostmann

open Complex Set MeasureTheory
open scoped Interval

noncomputable def smoothHorizontalIntegral (χ : PrimitiveComplexCharacter)
    (X y : ℝ) : ℂ :=
  ∫ σ in (-(1 / 2 : ℝ))..2,
    (-deriv χ.L ((σ : ℂ) + y * I) / χ.L ((σ : ℂ) + y * I)) *
      smoothContourWeight X ((σ : ℂ) + y * I)

theorem primeMeanMellin_decay_pow : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖primeMeanMellin s‖ ≤ C / (1 + |s.im|) ^ 8 := by
  obtain ⟨C, hC, hbound⟩ := primeMeanMellin_decay
  refine ⟨C, hC, ?_⟩
  intro s hs hs'
  have he : Real.exp (-8 * Real.log (1 + |s.im|)) = ((1 + |s.im|) ^ 8)⁻¹ := by
    rw [show -(8 : ℝ) * Real.log (1 + |s.im|) =
      -((8 : ℕ) * Real.log (1 + |s.im|)) by norm_num, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 1 + |s.im|)]
  simpa only [he, div_eq_mul_inv] using hbound s hs hs'

/-- The local logarithmic derivative is at most cubic, while the fixed test
has eighth-order Mellin decay. The resulting horizontal integrals decay to zero. -/
theorem exists_smooth_horizontal_bound (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 3 ≤ T → ∃ t : ℝ,
      T < t ∧ t < T + 1 ∧ (∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t) ∧
      ∀ y : ℝ, y = t ∨ y = -t →
        ‖smoothHorizontalIntegral χ X y‖ ≤ D / (T + 1) ^ 5 := by
  obtain ⟨K, hK, hheight⟩ := exists_character_horizontal_bound χ
  obtain ⟨C, hC, hmellin⟩ := primeMeanMellin_decay_pow
  refine ⟨20 * K * X ^ 2 * C, by positivity, ?_⟩
  intro T hT
  obtain ⟨t, ht, ht', hzero, hlog⟩ := hheight T hT
  refine ⟨t, ht, ht', hzero, ?_⟩
  intro y hy
  have hTpos : 0 < T + 1 := by linarith
  have htpos : 0 < t := by linarith
  have hyabs : |y| = t := by rcases hy with rfl | rfl <;> simp [abs_of_pos htpos]
  have hpoint (σ : ℝ) (hσ : σ ∈ uIcc (-(1 / 2 : ℝ)) 2) :
      ‖(-deriv χ.L ((σ : ℂ) + y * I) / χ.L ((σ : ℂ) + y * I)) *
        smoothContourWeight X ((σ : ℂ) + y * I)‖ ≤
          8 * K * X ^ 2 * C / (T + 1) ^ 5 := by
    rw [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 2)] at hσ
    let s : ℂ := (σ : ℂ) + y * I
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = y := by simp [s]
    have hcp : ‖(X : ℂ) ^ s‖ ≤ X ^ 2 := by
      rw [norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < X), hsre]
      exact (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ X) hσ.2).trans_eq
        (Real.rpow_two X)
    have hm : ‖primeMeanMellin s‖ ≤ C / (T + 1) ^ 8 := by
      apply (hmellin s (by rw [hsre]; exact hσ.1) (by rw [hsre]; exact hσ.2)).trans
      rw [hsim, hyabs]
      exact div_le_div_of_nonneg_left hC.le (pow_pos hTpos 8)
        (pow_le_pow_left₀ hTpos.le (by linarith) 8)
    have hl : ‖logDeriv χ.L s‖ ≤ 8 * K * (T + 1) ^ 3 := by
      apply (hlog y hy σ hσ).trans
      have hp : (T + 5) ^ 3 ≤ 8 * (T + 1) ^ 3 := by
        calc
          _ ≤ (2 * (T + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
          _ = _ := by ring
      nlinarith
    change ‖(-deriv χ.L s / χ.L s) * smoothContourWeight X s‖ ≤ _
    rw [norm_mul, smoothContourWeight, norm_mul]
    have hn : ‖-deriv χ.L s / χ.L s‖ = ‖logDeriv χ.L s‖ := by
      simp [logDeriv_apply, neg_div]
    rw [hn]
    calc
      _ ≤ (8 * K * (T + 1) ^ 3) * (X ^ 2 * (C / (T + 1) ^ 8)) :=
        mul_le_mul hl (mul_le_mul hcp hm (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = _ := by field_simp
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(1 / 2 : ℝ)) (b := 2)
    (C := 8 * K * X ^ 2 * C / (T + 1) ^ 5)
    (f := fun σ : ℝ => (-deriv χ.L ((σ : ℂ) + y * I) / χ.L ((σ : ℂ) + y * I)) *
      smoothContourWeight X ((σ : ℂ) + y * I))
    (fun σ hσ => hpoint σ (uIoc_subset_uIcc hσ))
  change ‖smoothHorizontalIntegral χ X y‖ ≤ _ at hi
  norm_num at hi
  convert hi using 1; ring

end Ostmann

end OAI
