import OAI.NumberTheory.Ostmann.Construction.ScheduledDiagonalDecomposition
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorMatchingCount

namespace OAI

/-! # The actual pivot diagonal splits by the anchor code -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledAnchorMatchingSet_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    scheduledAnchorMatchingSet role 0 m word = cellPreservingMatchings (scheduledBulkLabel role 0) := by
  apply Finset.Subset.antisymm (scheduledAnchorMatchingSet_subset role 0 m word)
  intro e he
  apply (mem_scheduledAnchorMatchingSet role 0 m word e).mpr
  refine ⟨(mem_cellPreservingMatchings _ _).mp he, ?_⟩
  intro x
  funext i
  exact Fin.elim0 i

theorem scheduled_anchor_diagonal_split {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (p : I) (n m : ℕ)
    (word : Fin m ≃ {i : Σ a, Fin (size a) // role i.1 = .word})
    (hdisjoint : ∀ a b : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      scheduledBulkLabel _ n a ≠ scheduledBulkLabel _ n b →
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hlarge : ∀ q ∈ P, V n < q) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let A := scheduledAnchorMatchingSet ρ n m word
    let B := cellPreservingMatchings (scheduledBulkLabel ρ n) \ A
    scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p n =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot n P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) A M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot n P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) B M).re := by
  exact scheduledConstituentDiagonal_split role size χ κ pivot P hP Q lo hi V pivotBound leaf center p n
    (scheduledBulkLabel _ n) hdisjoint hzero hlarge _
    (scheduledAnchorMatchingSet_subset _ n m word)

end Ostmann

end OAI
