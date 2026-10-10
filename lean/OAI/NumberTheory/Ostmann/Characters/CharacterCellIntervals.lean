import OAI.NumberTheory.Ostmann.Construction.PrimeCellProductIntervals

namespace OAI

/-! # The pivot lists, two anchors and filler give the actual character cells -/
namespace Ostmann
open scoped Classical BigOperators

/-- A selected ordered list is used once in each signed copy. -/
def characterCellIndex {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) :
    (v : CharacterCell k) → Fin (characterCellSize (fun j => (w j).length) u.length v) → ℕ
  | .inl j, i => (w j).get i
  | .inr (.inl (j, b)), _ => a j b
  | .inr (.inr _), i => u.get i

theorem characterCellIndex_target {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) (J F E : ℝ) (T : Fin k → ℝ)
    (hE : 0 ≤ E) (hw : ∀ j, |((w j).sum : ℝ) - T j| ≤ E)
    (hu : |(u.sum : ℝ) - F| ≤ E) (v : CharacterCell k) :
    |(∑ i, (characterCellIndex w a u v i : ℝ)) -
      characterLogCenter J T (fun j b => (a j b : ℝ)) F (true, some v)| ≤ E := by
  cases v with
  | inl j =>
    have he : (∑ i : Fin (w j).length, (w j).get i) = (w j).sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    change |(∑ i : Fin (w j).length, ((w j).get i : ℝ)) - T j| ≤ E
    simpa only [← Nat.cast_sum, he] using hw j
  | inr v =>
    cases v with
    | inl x =>
      rcases x with ⟨j, b⟩
      change |(∑ _i : Fin 1, (a j b : ℝ)) - (a j b : ℝ)| ≤ E
      simpa using hE
    | inr x =>
      have he : (∑ i : Fin u.length, u.get i) = u.sum := by
        rw [← List.sum_ofFn, List.ofFn_get]
      change |(∑ i : Fin u.length, (u.get i : ℝ)) - F| ≤ E
      simpa only [← Nat.cast_sum, he] using hu

theorem characterCellIndex_product_bounds {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) (J F E c : ℝ) (T : Fin k → ℝ)
    (hE : 0 ≤ E) (hw : ∀ j, |((w j).sum : ℝ) - T j| ≤ E)
    (hu : |(u.sum : ℝ) - F| ≤ E)
    (hc : ∀ v, E + (characterCellSize (fun j => (w j).length) u.length v : ℝ) ≤ c) :
    ∀ v : CharacterCell k,
      Real.exp (characterLogCenter J T (fun j b => (a j b : ℝ)) F (true, some v) - c) ≤
        (∏ i, primeCellLower (characterCellIndex w a u v i) : ℕ) ∧
      (∏ i, primeCellUpper (characterCellIndex w a u v i) : ℕ) ≤
        Real.exp (characterLogCenter J T (fun j b => (a j b : ℝ)) F (true, some v) + c) := by
  intro v
  exact primeCell_target_products (characterCellIndex w a u v) _ E c
    (characterCellIndex_target w a u J F E T hE hw hu v) (hc v)

theorem characterCellIndex_prime_bounds {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ v, Fin (characterCellSize (fun j => (w j).length) u.length v)) → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P)
    (hcell : ∀ v i p, p ∈ Q ⟨v, i⟩ → primeLogIndex p = characterCellIndex w a u v i) :
    ∀ v i p, p ∈ Q ⟨v, i⟩ →
      primeCellLower (characterCellIndex w a u v i) ≤ p ∧
        p ≤ primeCellUpper (characterCellIndex w a u v i) := by
  intro v i p hp
  exact primeCell_interval p _ (hP p (hQ ⟨v, i⟩ hp)) (hcell v i p hp)

end Ostmann

end OAI
