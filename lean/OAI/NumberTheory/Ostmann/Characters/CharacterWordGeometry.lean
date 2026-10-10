import OAI.NumberTheory.Ostmann.Characters.CharacterWordIntervals
import OAI.NumberTheory.Ostmann.Characters.CharacterDiagonalGap

namespace OAI

/-! # The original word bin and selected cell endpoints supply every transfer gap -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_word_geometry (k : ℕ) (B z c : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ J : ℕ, ∀ a : Fin k → Bool → ℝ, ∀ F : ℝ,
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let C := characterRangeError k c
    ∀ cl ch : CharacterCell k → ℕ,
    (∀ v, Real.exp (characterLogCenter J T a F (true, some v) - c) ≤ cl v) →
    (∀ v, (ch v : ℝ) ≤ Real.exp (characterLogCenter J T a F (true, some v) + c)) →
    let lo := initialWordAtomLower J cl
    let hi := initialWordAtomUpper J ch
    ∀ (n : ℕ) (hn : n < k),
      0 < lo (characterPivotAtom ⟨n, hn⟩) ∧
      hi (characterPivotAtom ⟨n, hn⟩) ≤ naturalProductCap (T ⟨n, hn⟩ + C) ∧
      2 * naturalProductCap (T ⟨n, hn⟩ + C) *
        naturalTransferCutoff (characterBaseGap B z m) m n <
          ∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) ∧
      2 * naturalTransferCutoff (characterBaseGap B z m) m n *
          (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val)) ≤
        naturalTransferCutoff (characterBaseGap B z m) m (n + 1) *
          lo (characterPivotAtom ⟨n, hn⟩) ∧
      Real.exp (characterPivotGap B z m n - 2 * C) *
          (naturalProductCap (T ⟨n, hn⟩ + C) : ℝ) ≤
        ∏ h : CopyScheduleH (characterRole k) n, (lo (copyScheduleOrigin n h.val) : ℝ) := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  filter_upwards [eventual_character_interval_geometry k B z c hB hz hc0] with m hm
  intro J a F T C cl ch hlo hhi lo hi n hn
  have he := character_word_interval_errors J c hc T a F cl ch hlo hhi
  have hg := hm J a F lo hi he.1 he.2 n hn
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
    character_diagonal_product_gap hn J B z m F c hc0 a lo hi he.1 he.2⟩

end Ostmann

end OAI
