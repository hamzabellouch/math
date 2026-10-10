import OAI.NumberTheory.Ostmann.Construction.ScheduledArithmeticIteration
import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonalSupport

namespace OAI

/-! # The literal iteration diagonal splits into its original-prior matching sums -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem scheduledConstituentDiagonal_split {I K : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (lo hi : I → ℕ) (V pivotBound : ℕ → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (p : I) (j : ℕ)
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) j → K)
    (hdisjoint : ∀ a b, label a ≠ label b →
      Disjoint (Q (copyScheduleOrigin j a.val)) (Q (copyScheduleOrigin j b.val)))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hlarge : ∀ q ∈ P, V j < q)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) j)))
    (hS : S ⊆ cellPreservingMatchings label) :
    scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p j =
      (∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot j P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j) S M).re) +
      ∑ M ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily role size χ κ pivot j P hP Q V pivotBound
          (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j)
          (cellPreservingMatchings label \ S) M).re := by
  have hsmall (d : ScheduledFrequencyIndex V j) (q : ℕ) (hq : q ∈ P) :
      (frequencyRoot j (scheduledFrequencyHistory V j d)).natAbs < q :=
    (scheduledFrequencyHistory_root_bound V j d).trans_lt (hlarge q hq)
  have hM (M : ℕ) := congrArg Complex.re
    (constituentPivotDiagonal_average_split role size χ κ pivot j P hP Q V pivotBound
      (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V j)
      label hdisjoint center M hzero hsmall S hS)
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re] at hM
  unfold scheduledConstituentDiagonal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hM]
  exact Finset.sum_add_distrib

end Ostmann

end OAI
