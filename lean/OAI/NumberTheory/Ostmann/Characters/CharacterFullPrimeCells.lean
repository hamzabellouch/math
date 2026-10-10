import OAI.NumberTheory.Ostmann.Characters.CharacterSelectedBulk
import OAI.NumberTheory.Ostmann.Construction.InitialWordPriorIntervals

namespace OAI

/-! # The original signed product law from its word and nonword prime cells -/
namespace Ostmann
open scoped Classical BigOperators

/-- Both signs use the same marginal. Signs change the characters, never the
original positive harmonic measure. -/
noncomputable def characterFullPrimeCells {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ) :
    (Σ v, Fin (characterSize m r f v)) → Finset ℕ
  | ⟨(_, none), i⟩ => Q i
  | ⟨(_, some v), i⟩ => R v i

@[simp] theorem characterFullPrimeCells_bulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ) (i : Fin m) :
    characterFullPrimeCells m r f Q R (characterBulk m r f i) = Q i.succ := rfl

@[simp] theorem characterFullPrimeCells_top {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ) :
    characterFullPrimeCells m r f Q R (characterTop m r f) = Q 0 := rfl

@[simp] theorem characterFullPrimeCells_anchor {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (j : Fin k) (b : Bool) :
    characterFullPrimeCells m r f Q R (characterAnchor m r f j b) =
      R (.inr (.inl (j, b))) ⟨0, by change 0 < 1; omega⟩ := rfl

theorem characterFullPrimeCells_subset {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (P : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ v i, R v i ⊆ P) :
    ∀ i, characterFullPrimeCells m r f Q R i ⊆ P := by
  rintro ⟨⟨b, v⟩, i⟩
  cases v with
  | none => exact hQ i
  | some v => exact hR v i

theorem characterFullPrimeCells_mass {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i, 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹)
    (hR : ∀ v i, 0 < ∑ p ∈ R v i, (p : ℝ)⁻¹) :
    ∀ i, 0 < ∑ p ∈ characterFullPrimeCells m r f Q R i, (p : ℝ)⁻¹ := by
  rintro ⟨⟨b, v⟩, i⟩
  cases v with
  | none => exact hQ i
  | some v => exact hR v i

/-- This equality identifies the literal scheduled law with the two copies
of the original word followed by the flattened nonword cells. -/
theorem characterFullPrimeCells_source {k : ℕ} (m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (i : Σ v, Fin (characterSize m r f v)) :
    Fin.append
      (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
      (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i) =
        characterFullPrimeCells m r f Q R i := by
  rcases i with ⟨⟨b, v⟩, i⟩
  cases v with
  | none =>
    cases b with
    | false =>
      change Fin.append
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        ((((show Fin (m + 1) from i).castAdd nc).natAdd ((m + 1) + nc))) = Q i
      rw [Fin.append_right]
      exact Fin.append_left Q _ (show Fin (m + 1) from i)
    | true =>
      change Fin.append
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        (Fin.append Q (fun j => R (cell.symm j).1 (cell.symm j).2))
        ((((show Fin (m + 1) from i).castAdd nc).castAdd ((m + 1) + nc))) = Q i
      rw [Fin.append_left]
      exact Fin.append_left Q _ (show Fin (m + 1) from i)
  | some v =>
    have h := initialWordTuple_cell_set (m + 1) nc
      (characterCellSize r f) cell Q (fun j => R (cell.symm j).1 (cell.symm j).2) b v i
    rw [cell.symm_apply_apply] at h
    exact h

theorem characterFullPrimeCells_probability {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (P : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ v i, R v i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹)
    (hRmass : ∀ v i, 0 < ∑ p ∈ R v i, (p : ℝ)⁻¹) :
    ∀ i, (∑ p : P, primeSubsetPrior P (characterFullPrimeCells m r f Q R i) p) = 1 := by
  intro i
  exact primeSubsetPrior_mass P _ (characterFullPrimeCells_subset m r f P Q R hQ hR i)
    (characterFullPrimeCells_mass m r f Q R hQmass hRmass i).ne'

end Ostmann

end OAI
