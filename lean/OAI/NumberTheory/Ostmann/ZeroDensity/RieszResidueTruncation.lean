import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedRieszTails
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszTruncation

namespace OAI

/-! # Truncation while retaining the precise main residue -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem riesz_residue_truncation (f : ℂ → ℂ) (X b M T : ℝ) (v : ℂ)
    (hX : 0 < X) (hb : 1 ≤ b) (hM : 0 ≤ M) (hT : 0 < T)
    (hc : Continuous (fun t : ℝ => f (rieszMellinLine b t)))
    (hbound : ∀ t : ℝ, ‖f (rieszMellinLine b t)‖ ≤ M) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, f (rieszMellinLine b t) * rieszVerticalWeight X b t) - v‖ ≤
      ‖(∫ t in -T..T, f (rieszMellinLine b t) * rieszVerticalWeight X b t) -
          ((2 * Real.pi : ℝ) : ℂ) * v‖ + 2 * M * X ^ b / T := by
  let F : ℝ → ℂ := fun t => f (rieszMellinLine b t) * rieszVerticalWeight X b t
  let τ : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let q : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hnorm : ‖τ‖ ≤ 1 := by
    dsimp [τ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [Real.pi_gt_three])
  have hτ : τ * q = 1 := by
    dsimp [τ, q]
    norm_cast
    exact div_mul_cancel₀ 1 (by positivity : 2 * Real.pi ≠ 0)
  have hi : Integrable F := weightedRiesz_integrable f X b M hX hb hc hbound
  obtain ⟨hp, hn⟩ := weightedRiesz_both_tails f X b M T hX hM hT hbound
  have he : τ * (∫ t : ℝ, F t) - v = τ *
      ((∫ t in Iic (-T), F t) + ((∫ t in -T..T, F t) - q * v) + (∫ t in Ioi T, F t)) := by
    rw [integral_three_parts F hi T]
    linear_combination (congrArg (fun z : ℂ => z * v) hτ)
  change ‖τ * (∫ t : ℝ, F t) - v‖ ≤ ‖(∫ t in -T..T, F t) - q * v‖ + _
  rw [he, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans
  have hh := (norm_add_le ((∫ t in Iic (-T), F t) + ((∫ t in -T..T, F t) - q * v))
    (∫ t in Ioi T, F t)).trans
    (add_le_add (norm_add_le (∫ t in Iic (-T), F t) ((∫ t in -T..T, F t) - q * v)) le_rfl)
  change ‖∫ t in Ioi T, F t‖ ≤ _ at hp
  change ‖∫ t in Iic (-T), F t‖ ≤ _ at hn
  calc
    _ ≤ ‖∫ t in Iic (-T), F t‖ + ‖(∫ t in -T..T, F t) - q * v‖ +
        ‖∫ t in Ioi T, F t‖ := hh
    _ ≤ M * X ^ b / T + ‖(∫ t in -T..T, F t) - q * v‖ + M * X ^ b / T :=
      add_le_add (add_le_add hn le_rfl) hp
    _ = _ := by ring

end Ostmann

end OAI
