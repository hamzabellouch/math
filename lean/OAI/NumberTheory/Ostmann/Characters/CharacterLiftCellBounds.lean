import OAI.NumberTheory.Ostmann.Characters.CharacterFullPrimeCells

namespace OAI

/-! # Lift actual nonword intervals to both signed copies -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterLiftCellBound {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f d : ℕ)
    (bound : (Σ v, Fin (characterCellSize r f v)) → ℕ) :
    (Σ v, Fin (characterSize m r f v)) → ℕ
  | ⟨(_, none), _⟩ => d
  | ⟨(_, some v), i⟩ => bound ⟨v, i⟩

@[simp] theorem characterLiftCellBound_nonword {k : ℕ} (m : ℕ) (r : Fin k → ℕ)
    (f d : ℕ) (bound : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (sgn : Bool) (v : CharacterCell k) (i : Fin (characterCellSize r f v)) :
    characterLiftCellBound m r f d bound ⟨(sgn, some v), i⟩ = bound ⟨v, i⟩ := rfl

theorem characterLiftCellBound_support {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (P : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQP : ∀ i, Q i ⊆ P)
    (lo hi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ v i p, p ∈ R v i → lo ⟨v, i⟩ ≤ p ∧ p ≤ hi ⟨v, i⟩) :
    ∀ i p, p ∈ characterFullPrimeCells m r f Q R i →
      characterLiftCellBound m r f 0 lo i ≤ p ∧
      p ≤ characterLiftCellBound m r f (P.sup id) hi i := by
  rintro ⟨⟨sgn, v⟩, i⟩ p hp
  cases v with
  | none => exact ⟨Nat.zero_le _, Finset.le_sup (f := id) (hQP i hp)⟩
  | some v => exact hcell v i p hp

end Ostmann

end OAI
