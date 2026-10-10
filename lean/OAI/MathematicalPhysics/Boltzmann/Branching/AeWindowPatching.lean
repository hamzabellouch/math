import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Encodable

namespace OAI

/-! # A countable family of short multiplicative windows determines a common time-pair set -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem ae_patch_multiplicative_windows {c R : ℝ} (hc : 0 < c)
    {P : ℝ → ℝ → Prop}
    (hlocal : ∀ b : ℚ, ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      R < (b:ℝ) → s ∈ Ioo (b:ℝ) ((1+c)*(b:ℝ)) →
        t ∈ Ioo (b:ℝ) ((1+c)*(b:ℝ)) → P s t) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, R < s → s < t → t < (1+c)*s → P s t := by
  have hsall : ∀ᵐ s ∂volume, ∀ b : ℚ, ∀ᵐ t ∂volume,
      R < (b:ℝ) → s ∈ Ioo (b:ℝ) ((1+c)*(b:ℝ)) →
        t ∈ Ioo (b:ℝ) ((1+c)*(b:ℝ)) → P s t := ae_all_iff.mpr hlocal
  filter_upwards [hsall] with s hs
  have htall : ∀ᵐ t ∂volume, ∀ b : ℚ,
      R < (b:ℝ) → s ∈ Ioo (b:ℝ) ((1+c)*(b:ℝ)) →
        t ∈ Ioo (b:ℝ) ((1+c)*(b:ℝ)) → P s t := ae_all_iff.mpr hs
  filter_upwards [htall] with t ht
  intro hRs hst htu
  have hU : 0 < 1+c := by linarith
  have hlo : max R (t/(1+c)) < s :=
    max_lt_iff.mpr ⟨hRs,(div_lt_iff₀ hU).mpr (by simpa only [mul_comm] using htu)⟩
  obtain ⟨b,hblo,hbs⟩ := exists_rat_btwn hlo
  have hRb := (le_max_left R (t/(1+c))).trans_lt hblo
  have hbt : t < (1+c)*(b:ℝ) := by
    have hh := (div_lt_iff₀ hU).mp ((le_max_right R (t/(1+c))).trans_lt hblo)
    simpa only [mul_comm] using hh
  exact ht b hRb ⟨hbs,hst.trans hbt⟩ ⟨hbs.trans hst,hbt⟩

end BoltzmannNonuniqueness

end

end OAI
