import OAI.NumberTheory.Ostmann.Characters.CharacterBulkSeparation
import OAI.NumberTheory.Ostmann.ZeroDensity.InitialIntervalZero

namespace OAI

/-! # The literal diagonal of the original signed character prior -/
namespace Ostmann
open scoped Classical BigOperators

/-- The split uses disjointness only between the true bulk and the remaining
original cells. The selected word bin removes the zero frequency. -/
theorem character_literal_diagonal_split {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ)
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
    (hlarge : ∀ q ∈ P, V n < q) :
    let lo := initialWordAtomLower J cellLo
    let hi := initialWordAtomUpper J cellHi
    let Q₀ := characterFullPrimeCells m r f Q R
    let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
    let A := selectedAnchorMatchingSet ρ n m (characterBulk m r f) (characterBulk_role m r f)
    let B := cellPreservingMatchings (selectedBulkLabel ρ n m
      (characterBulk m r f) (characterBulk_role m r f)) \ A
    scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ pivot P hP Q₀
      lo hi V cap leaf center p n =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ κ pivot n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi) leaf
          (scheduledFrequencyHistory V n) A M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ κ pivot n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi) leaf
          (scheduledFrequencyHistory V n) B M).re := by
  intro lo hi Q₀ ρ A B
  exact selected_anchor_diagonal_split (characterRole k) (characterSize m r f) χ κ pivot
    P hP Q₀ lo hi V cap leaf center p n m (characterBulk m r f) (characterBulk_role m r f)
    (character_bulk_label_disjoint m r f n Q U R hQ htop hR)
    (fullAtomTransferWeight_zero_of_interval (characterRole k) lo hi V cap leaf
      (true, none) (initialWordAtomLower_word_gt_one J hJ cellLo true)) hlarge

end Ostmann

end OAI
