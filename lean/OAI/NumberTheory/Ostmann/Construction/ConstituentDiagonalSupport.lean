import OAI.NumberTheory.Ostmann.Construction.PrimeMatchingSupport
import OAI.NumberTheory.Ostmann.Construction.ScheduledBulkMatchingCount
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # Exact bad/good splitting of the original-prior pivot diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem scheduledBadMatchingSet_subset {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    scheduledBadMatchingSet role n m word ⊆ cellPreservingMatchings (scheduledBulkLabel role n) := by
  intro e he
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
  exact (mem_cellPreservingMatchings _ _).mpr f.val.property

noncomputable def scheduledGoodMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) : Finset (Equiv.Perm (CopyScheduleH role n)) :=
  cellPreservingMatchings (scheduledBulkLabel role n) \ scheduledBadMatchingSet role n m word

section
variable {I D K : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

noncomputable def constituentMatchingFamily
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (M : ℕ) : ℂ :=
  ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
    ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
    ∑ e ∈ S, primeMatchingContribution P (fun d => frequencyRoot n (hist d))
      (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M) e

theorem constituentCharacterCorrelation_cell_split
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → K)
    (hdisjoint : ∀ i j, label i ≠ label j →
      Disjoint (Q (copyScheduleOrigin n i.val)) (Q (copyScheduleOrigin n j.val)))
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (hS : S ⊆ cellPreservingMatchings label) :
    let c := constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M
    primePermutationCorrelation P (fun d => frequencyRoot n (hist d)) c =
      (∑ e ∈ S, primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e) +
      ∑ e ∈ cellPreservingMatchings label \ S,
        primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e := by
  intro c
  generalize hcf : c = c'
  let H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  let : Fintype H := Fintype.ofFinite H
  let : Fintype D := Fintype.ofFinite D
  let F : ((H → P) × D) → ℂ :=
    constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M
  have hc (l : H → P) (d : D) : c' (l, d) =
      ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h) : ℝ) : ℂ) * F (l, d) := by
    rw [← hcf]
    simpa only [finite_univ_canonical] using
      (constituentCharacterCoefficient_factor role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d))
  have hS' : S ⊆ cellPreservingMatchings label := by
    simpa only [cellPreservingMatchings_fintype] using hS
  have hs := primePermutationCorrelation_cell_split P
    (fun h : H => Q (copyScheduleOrigin n h.val)) label hdisjoint
    (fun d => frequencyRoot n (hist d)) c' F hc S hS'
  simpa only [primePermutationCorrelation_fintype, primeMatchingContribution_fintype,
    cellPreservingMatchings_fintype, finset_sdiff_canonical] using hs

theorem constituentPivotDiagonal_cell_split
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → K)
    (hdisjoint : ∀ i j, label i ≠ label j →
      Disjoint (Q (copyScheduleOrigin n i.val)) (Q (copyScheduleOrigin n j.val)))
    (center : ∀ p : ℕ, ZMod p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (hS : S ⊆ cellPreservingMatchings label) :
    let c := constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M
    constituentPivotDiagonal role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M =
      (∑ e ∈ S, primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e) +
      ∑ e ∈ cellPreservingMatchings label \ S,
        primeMatchingContribution P (fun d => frequencyRoot n (hist d)) c e := by
  exact (constituentPivotDiagonal_characters role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center u M hzero hsmall).trans
    (constituentCharacterCorrelation_cell_split role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist label hdisjoint u M S hS)

theorem constituentPivotDiagonal_average_split
    (label : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → K)
    (hdisjoint : ∀ i j, label i ≠ label j →
      Disjoint (Q (copyScheduleOrigin n i.val)) (Q (copyScheduleOrigin n j.val)))
    (center : ∀ p : ℕ, ZMod p) (M : ℕ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (hS : S ⊆ cellPreservingMatchings label) :
    (∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
      ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
      constituentPivotDiagonal role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center u M) =
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M +
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist
      (cellPreservingMatchings label \ S) M := by
  simp_rw [constituentPivotDiagonal_cell_split role size χ κ pivot n P hP Q childBound pivotBound
    ranges leaf hist label hdisjoint center _ M hzero hsmall S hS, mul_add]
  exact Finset.sum_add_distrib

end
end Ostmann

end OAI
