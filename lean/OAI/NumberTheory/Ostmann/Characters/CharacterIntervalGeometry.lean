import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCenters

namespace OAI

/-! # The constructed character targets satisfy the two integer transfer inequalities -/
namespace Ostmann
open scoped Classical BigOperators
open Filter

noncomputable def characterRangeError (k : ℕ) (c : ℝ) : ℝ :=
  ((2 : ℝ) ^ k + k + 2) * c

/-- The threshold is uniform in the selected word bin, anchors and target
centers. Only the fixed depth and bounded cell errors enter it. -/
theorem eventual_character_interval_geometry (k : ℕ) (B z c : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ J : ℝ, ∀ a : Fin k → Bool → ℝ, ∀ F : ℝ,
    let Δ := fun j : Fin k => characterPivotGap B z m j.val
    let A := fun j => a j false + a j true
    let T := characterPivotTarget k J A Δ
    let w := characterLogCenter J T a F
    let C := characterRangeError k c
    ∀ lo hi : CharacterRole k → ℕ,
    (∀ i, Real.exp (w i - c) ≤ lo i) →
    (∀ i, (hi i : ℝ) ≤ Real.exp (w i + c)) →
    ∀ (n : ℕ) (hn : n < k),
      0 < lo (characterPivotAtom ⟨n, hn⟩) ∧
      hi (characterPivotAtom ⟨n, hn⟩) ≤ naturalProductCap (T ⟨n, hn⟩ + C) ∧
      2 * naturalProductCap (T ⟨n, hn⟩ + C) *
        naturalTransferCutoff (characterBaseGap B z m) m n <
          ∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) ∧
      2 * naturalTransferCutoff (characterBaseGap B z m) m n *
          (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val)) ≤
        naturalTransferCutoff (characterBaseGap B z m) m (n + 1) *
          lo (characterPivotAtom ⟨n, hn⟩) := by
  filter_upwards [eventually_rounded_schedule_ranges (characterRangeError k c),
    eventually_ge_atTop (0 : ℝ)] with m hm hm0
  intro J a F Δ A T w C lo hi hlo hhi n hn
  have hcC : c ≤ C := by
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hh : 1 ≤ (2 : ℝ) ^ k + k + 2 := by
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hmul := mul_le_mul_of_nonneg_right hh hc
    change c ≤ ((2 : ℝ) ^ k + k + 2) * c
    simpa only [one_mul] using hmul
  have hcenter : (∑ h : CopyScheduleH (characterRole k) n,
      w (copyScheduleOrigin n h.val)) = T ⟨n, hn⟩ + characterPivotGap B z m n :=
    character_H_target_center hn J B z m F a
  have hproducts := character_H_product_bounds hn w lo hi c hc hlo hhi
  change Real.exp (_ - C) ≤ _ ∧ _ ≤ Real.exp (_ + C) at hproducts
  rw [← character_H_sum hn w, hcenter] at hproducts
  have hM : Real.exp (T ⟨n, hn⟩ - C) ≤ lo (characterPivotAtom ⟨n, hn⟩) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) (hlo (characterPivotAtom ⟨n, hn⟩))
    change T ⟨n, hn⟩ - C ≤ T ⟨n, hn⟩ - c
    linarith
  have hpivot : hi (characterPivotAtom ⟨n, hn⟩) ≤ naturalProductCap (T ⟨n, hn⟩ + C) := by
    apply Nat.le_floor
    exact (hhi (characterPivotAtom ⟨n, hn⟩)).trans
      (Real.exp_le_exp.mpr (by change T ⟨n, hn⟩ + c ≤ T ⟨n, hn⟩ + C; linarith))
  have hΔ : 0 ≤ characterBaseGap B z m :=
    mul_nonneg (add_nonneg hB (mul_nonneg (by norm_num) (Real.log_nonneg hz))) hm0
  have hL : Real.exp (T ⟨n, hn⟩ + transferNextGap (characterBaseGap B z m) m n - C) ≤
      (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) : ℕ) :=
    hproducts.1
  have hK : (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val)) ≤
      naturalProductCap (T ⟨n, hn⟩ + transferNextGap (characterBaseGap B z m) m n + C) :=
    Nat.le_floor hproducts.2
  have hgeometry := hm (characterBaseGap B z m) hΔ n (T ⟨n, hn⟩ + 0)
    (lo (characterPivotAtom ⟨n, hn⟩)) (naturalProductCap (T ⟨n, hn⟩ + C))
    (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val))
    (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val))
    (by simpa only [add_zero] using hM) (by simp only [add_zero]; exact le_rfl)
    (by simpa only [add_zero] using hL) (by simpa only [add_zero] using hK)
  have hpos : 0 < lo (characterPivotAtom ⟨n, hn⟩) := by
    exact_mod_cast (Real.exp_pos _).trans_le hM
  exact ⟨hpos, hpivot, hgeometry.1, hgeometry.2⟩

end Ostmann

end OAI
