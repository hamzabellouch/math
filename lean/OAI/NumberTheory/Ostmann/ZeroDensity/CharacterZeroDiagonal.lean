import OAI.NumberTheory.Ostmann.Characters.CharacterLiteralDiagonal

namespace OAI

/-! # At depth zero every compatible matching preserves the empty anchor code -/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentMatchingFamily_empty {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n) (M : ℕ) :
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges
      leaf hist ∅ M = 0 := by
  simp only [constituentMatchingFamily, Finset.sum_empty, mul_zero, Finset.sum_const_zero]

theorem character_literal_diagonal_zero {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (U : Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i : Fin m, Q i.succ = U) (htop : Disjoint U (Q 0))
    (hR : ∀ v i, Disjoint U (R v i))
    (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (hJ : 0 < J) (cellLo cellHi : CharacterCell k → ℕ)
    (V cap : ℕ → ℕ) (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ)
    (center : ∀ p : ℕ, ZMod p) (p : CharacterRole k)
    (hlarge : ∀ q ∈ P, V 0 < q) :
    let lo := initialWordAtomLower J cellLo
    let hi := initialWordAtomUpper J cellHi
    let Q₀ := characterFullPrimeCells m r f Q R
    let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
    let A := selectedAnchorMatchingSet ρ 0 m (characterBulk m r f) (characterBulk_role m r f)
    scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ pivot P hP Q₀
      lo hi V cap leaf center p 0 =
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ κ pivot 0 P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi) leaf
          (scheduledFrequencyHistory V 0) A M).re := by
  have h := character_literal_diagonal_split m r f 0 Q U R hQ htop hR χ κ pivot P hP
    J hJ cellLo cellHi V cap leaf center p hlarge
  dsimp only at h ⊢
  have he : cellPreservingMatchings (selectedBulkLabel
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) 0 m
      (characterBulk m r f) (characterBulk_role m r f)) \
      selectedAnchorMatchingSet
        (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) 0 m
        (characterBulk m r f) (characterBulk_role m r f) = ∅ := by
    rw [selectedAnchorMatchingSet_zero, Finset.sdiff_self]
  rw [he] at h
  simpa only [constituentMatchingFamily_empty, Complex.zero_re, Finset.sum_const_zero,
    add_zero] using h

end Ostmann

end OAI
