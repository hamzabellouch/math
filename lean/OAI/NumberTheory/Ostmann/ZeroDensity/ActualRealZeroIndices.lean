import OAI.NumberTheory.Ostmann.ZeroDensity.FullHeightRegionComparison

namespace OAI

/-! # Locating every actual real zero in the faithful multiplicity enumeration -/

namespace Ostmann

open Complex

theorem PrimitiveRealZero.has_actual_index (e : PrimitiveRealZero) :
    ∃ i, (realCharacterActualZeros e.asRealCharacter).zeros i = (e.beta : ℂ) := by
  apply actualCharacterZeros_complete e.asRealCharacter.asComplex
  exact ⟨e.beta_pos, e.beta_lt_one, e.zero⟩

theorem PrimitiveRealZero.kernel_le_zero_sum (e : PrimitiveRealZero) (σ : ℝ)
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    1 / (σ - e.beta) ≤ shiftedRealCharacterZeroSum e.asRealCharacter (σ : ℂ) := by
  obtain ⟨i, hi⟩ := e.has_actual_index
  have hh := shifted_real_zero_term_le e.asRealCharacter (σ : ℂ) hσ hσ2 i
  rw [hi, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re] at hh
  simpa only [one_div] using hh

theorem PrimitiveRealZero.eq_of_character_beta {e f : PrimitiveRealZero}
    (hχ : e.asRealCharacter = f.asRealCharacter) (hβ : e.beta = f.beta) : e = f := by
  cases e
  cases f
  cases hχ
  cases hβ
  rfl

end Ostmann

end OAI
