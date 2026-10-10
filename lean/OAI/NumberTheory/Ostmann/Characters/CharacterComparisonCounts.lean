import OAI.NumberTheory.Ostmann.Characters.CharacterScheduleRoles
import OAI.NumberTheory.Ostmann.Arithmetic.AtomIntervalComplexity

namespace OAI

/-! # Concrete complexity bounds for the signed character comparison -/
namespace Ostmann
open scoped Classical

theorem characterSize_le (k m N : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, r j ≤ N) (hf : f ≤ N) (v : CharacterRole k) :
    characterSize m r f v ≤ m + N + 1 := by
  rcases v with ⟨b, v⟩
  cases v with
  | none => change m + 1 ≤ _; omega
  | some v =>
    rcases v with j | (a | u)
    · exact (hr j).trans (by omega)
    · change 1 ≤ _; omega
    · exact hf.trans (by omega)

theorem characterSize_linear_bound (m N : ℕ) :
    ((m + N + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 2) * (1 + (m : ℝ)) := by
  have hm := Nat.cast_nonneg (α := ℝ) m
  have hN := Nat.cast_nonneg (α := ℝ) N
  push_cast
  nlinarith

theorem character_interval_complexity (k n : ℕ) (hn : n ≤ k)
    (lo hi : CharacterRole k → ℕ) :
    (∀ j ≤ n, ∀ r ∈ atomIntervalRanges (characterRole k) lo hi j, r.atoms.length ≤ 1) ∧
      ∀ j ≤ n, (atomIntervalRanges (characterRole k) lo hi j).length ≤
        3 ^ k * Fintype.card (CharacterRole k) := by
  refine ⟨fun j _ r hr => (atomIntervalRanges_singleton _ lo hi j r hr).le, ?_⟩
  intro j hj
  exact atomIntervalRanges_length_le _ lo hi k j (hj.trans hn)

end Ostmann

end OAI
