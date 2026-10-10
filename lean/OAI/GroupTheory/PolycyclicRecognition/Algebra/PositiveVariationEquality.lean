import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace OAI

/-! # Equality in the positive-variation bound

Attaining the total positive variation at an intermediate time forces the
derivative to have the two ordered signs on either side of that time.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

/-- The equality case used at a maximizing time of each scalar weight of a
profile. The positive and negative variations are derived from the integrable
derivative; their vanishing is a conclusion. -/
theorem positive_variation_equality_signs
    (q : ℝ → ℝ) {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hq : IntervalIntegrable q volume a b)
    (heq : (∫ s in a..t, q s) = ∫ s in a..b, max (q s) 0) :
    (∀ᵐ s ∂volume.restrict (Ioc a t), 0 ≤ q s) ∧
      (∀ᵐ s ∂volume.restrict (Ioc t b), q s ≤ 0) := by
  have hp : IntervalIntegrable (fun s => max (q s) 0) volume a b :=
    ⟨hq.1.pos_part, hq.2.pos_part⟩
  have hn : IntervalIntegrable (fun s => max (-q s) 0) volume a b :=
    ⟨hq.1.neg_part, hq.2.neg_part⟩
  have hsub₁ : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le hat, uIcc_of_le (hat.trans htb)]
    exact Icc_subset_Icc le_rfl htb
  have hsub₂ : uIcc t b ⊆ uIcc a b := by
    rw [uIcc_of_le htb, uIcc_of_le (hat.trans htb)]
    exact Icc_subset_Icc hat le_rfl
  have hp₁ := hp.mono_set hsub₁
  have hp₂ := hp.mono_set hsub₂
  have hn₁ := hn.mono_set hsub₁
  have hparts : (∫ s in a..t, q s) =
      (∫ s in a..t, max (q s) 0) - ∫ s in a..t, max (-q s) 0 := by
    rw [← intervalIntegral.integral_sub hp₁ hn₁]
    apply intervalIntegral.integral_congr
    intro s _
    change q s = max (q s) 0 - max (-q s) 0
    by_cases hs : 0 ≤ q s
    · rw [max_eq_left hs, max_eq_right (neg_nonpos.mpr hs), sub_zero]
    · have hs' := le_of_not_ge hs
      rw [max_eq_right hs', max_eq_left (neg_nonneg.mpr hs')]
      ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hp₁ hp₂
  have hnonneg₁ : 0 ≤ ∫ s in a..t, max (-q s) 0 :=
    intervalIntegral.integral_nonneg_of_forall hat (fun _ => le_max_right _ _)
  have hnonneg₂ : 0 ≤ ∫ s in t..b, max (q s) 0 :=
    intervalIntegral.integral_nonneg_of_forall htb (fun _ => le_max_right _ _)
  have hzero₁ : (∫ s in a..t, max (-q s) 0) = 0 := by linarith
  have hzero₂ : (∫ s in t..b, max (q s) 0) = 0 := by linarith
  have hae₁ := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hat
    (Filter.Eventually.of_forall (fun s => le_max_right (-q s) 0)) hn₁).mp hzero₁
  have hae₂ := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae htb
    (Filter.Eventually.of_forall (fun s => le_max_right (q s) 0)) hp₂).mp hzero₂
  constructor
  · filter_upwards [hae₁] with s hs
    have := le_max_left (-q s) 0
    change max (-q s) 0 = 0 at hs
    linarith
  · filter_upwards [hae₂] with s hs
    have := le_max_left (q s) 0
    change max (q s) 0 = 0 at hs
    linarith

end PolycyclicRecognition

end

end OAI
