import OAI.NumberTheory.Ostmann.Construction.ScheduledDiagonalDecomposition
import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorMatchingCount

namespace OAI

/-! # The literal diagonal split by codes of the selected bulk -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedAnchorMatchingSet_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    selectedAnchorMatchingSet role 0 m bulk hbulk =
      cellPreservingMatchings (selectedBulkLabel role 0 m bulk hbulk) := by
  apply Finset.Subset.antisymm (selectedAnchorMatchingSet_subset role 0 m bulk hbulk)
  intro e he
  apply (mem_selectedAnchorMatchingSet role 0 m bulk hbulk e).mpr
  refine ⟨(mem_cellPreservingMatchings _ _).mp he, ?_⟩
  intro x
  funext i
  exact Fin.elim0 i

theorem selected_anchor_diagonal_split {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (p : I) (n m : ℕ)
    (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, role (bulk i).1 = .word)
    (hdisjoint : ∀ a b : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      selectedBulkLabel _ n m bulk hbulk a ≠ selectedBulkLabel _ n m bulk hbulk b →
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hlarge : ∀ q ∈ P, V n < q) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let A := selectedAnchorMatchingSet ρ n m bulk hbulk
    let B := cellPreservingMatchings (selectedBulkLabel ρ n m bulk hbulk) \ A
    scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p n =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot n P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) A M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot n P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) B M).re := by
  exact scheduledConstituentDiagonal_split role size χ κ pivot P hP Q lo hi V pivotBound leaf center p n
    (selectedBulkLabel _ n m bulk hbulk) hdisjoint hzero hlarge _
    (selectedAnchorMatchingSet_subset _ n m bulk hbulk)

end Ostmann

end OAI
