import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace OAI

namespace Invariant233.PrescribedPhaseRealization

def spliceFrequency (old new : ℕ → ℕ) (p : ℕ) (i : ℕ) : ℕ :=
  if i ≤ p then old i else new (i - p)

theorem spliceFrequency_eq_old (old new : ℕ → ℕ) {p i : ℕ} (hi : i ≤ p) :
    spliceFrequency old new p i = old i := by
  simp [spliceFrequency, hi]

theorem spliceFrequency_eq_new (old new : ℕ → ℕ) {p i : ℕ}
    (hboundary : new 0 = old p) (hi : p ≤ i) :
    spliceFrequency old new p i = new (i - p) := by
  rcases eq_or_lt_of_le hi with rfl | hi
  · simp [spliceFrequency, hboundary]
  · simp [spliceFrequency, Nat.not_le.mpr hi]

@[simp] theorem spliceFrequency_add (old new : ℕ → ℕ) (p i : ℕ)
    (hboundary : new 0 = old p) :
    spliceFrequency old new p (p + i) = new i := by
  simpa using spliceFrequency_eq_new old new hboundary (Nat.le_add_right p i)

theorem spliceFrequency_pos (old new : ℕ → ℕ) (p : ℕ)
    (hold : ∀ i ≤ p, 0 < old i) (hnew : ∀ i, 0 < new i) :
    ∀ i, 0 < spliceFrequency old new p i := by
  intro i
  by_cases hi : i ≤ p
  · simpa [spliceFrequency, hi] using hold i hi
  · simpa [spliceFrequency, hi] using hnew (i - p)

theorem spliceFrequency_strictMono (old new : ℕ → ℕ) (p : ℕ)
    (hboundary : new 0 = old p)
    (hold : ∀ i < p, old i < old (i + 1)) (hnew : StrictMono new) :
    StrictMono (spliceFrequency old new p) := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hi : i < p
  · rw [spliceFrequency_eq_old old new (by omega),
      spliceFrequency_eq_old old new (by omega)]
    exact hold i hi
  · rw [spliceFrequency_eq_new old new hboundary (by omega),
      spliceFrequency_eq_new old new hboundary (by omega)]
    apply hnew
    omega

theorem spliceFrequency_divisible (old new : ℕ → ℕ) (p : ℕ)
    (hboundary : new 0 = old p)
    (hold : ∀ i < p, old i ∣ old (i + 1))
    (hnew : ∀ i, new i ∣ new (i + 1)) :
    ∀ i, spliceFrequency old new p i ∣ spliceFrequency old new p (i + 1) := by
  intro i
  by_cases hi : i < p
  · rw [spliceFrequency_eq_old old new (by omega),
      spliceFrequency_eq_old old new (by omega)]
    exact hold i hi
  · rw [spliceFrequency_eq_new old new hboundary (by omega),
      spliceFrequency_eq_new old new hboundary (by omega)]
    have he : i + 1 - p = (i - p) + 1 := by omega
    rw [he]
    exact hnew (i - p)

theorem spliceFrequency_ratio (old new : ℕ → ℕ) (p i : ℕ)
    (hboundary : new 0 = old p) :
    (spliceFrequency old new p (p + i + 1) : ℝ) /
        spliceFrequency old new p (p + i) = (new (i + 1) : ℝ) / new i := by
  rw [Nat.add_assoc, spliceFrequency_add old new p (i + 1) hboundary,
    spliceFrequency_add old new p i hboundary]

end Invariant233.PrescribedPhaseRealization

end OAI
