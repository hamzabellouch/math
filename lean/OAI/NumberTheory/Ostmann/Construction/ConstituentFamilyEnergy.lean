import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonalSupport
import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingAverage
import OAI.NumberTheory.Ostmann.Construction.DiagonalEndpointCancellation

namespace OAI

/-! # Original-prior matching energy after the external pivot is summed -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

noncomputable def constituentHistoryEnergy (M : ℕ) : ℝ :=
  ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
    (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
    ∑ d : D, ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
      (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
      ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2

theorem constituentMatchingFamily_norm_le {R : Type*} [Fintype R]
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (lo : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℝ)
    (hlo : ∀ h, 0 < lo h)
    (hcell : ∀ h p, p ∈ Q (copyScheduleOrigin n h.val) → lo h ≤ (p : ℝ)) :
    ‖constituentMatchingFamily role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist S M‖ ≤
      (S.card : ℝ) * ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
        (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * (∏ h, lo h)⁻¹) *
        constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M := by
  have h := constituent_matching_family_energy_bound role size χ κ pivot hκ n P hP Q
    childBound pivotBound ranges leaf hist hhist root (fun d d' hd => (hroot d d').mp hd)
    M S lo hlo hcell
  simpa only [constituentMatchingFamily, primeMatchingContribution, constituentHistoryEnergy, hroot, finite_univ_canonical] using h

theorem constituentMatchingFamily_interval_le {R : Type*} [Fintype R]
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (lo : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℝ)
    (hlo : ∀ h, 0 < lo h)
    (hcell : ∀ h p, p ∈ Q (copyScheduleOrigin n h.val) → lo h ≤ (p : ℝ))
    (a b : ℕ) (ha : 0 < a) (gap E : ℝ) (hE : 0 ≤ E)
    (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, lo h)
    (henergy : ∀ M ∈ Finset.Icc a b,
      constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M ≤ E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist S M).re) ≤
      Real.exp (-gap) * ((S.card : ℝ) *
        ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * E := by
  let Z : ℝ := ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
    (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹
  have hZ : 0 ≤ Z := Finset.prod_nonneg fun h _ => inv_nonneg.mpr
    (Finset.sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  apply finite_pivot_sum_bound a b ha
    (fun M => constituentMatchingFamily role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist S M)
    ((S.card : ℝ) * Z) E gap (mul_nonneg (Nat.cast_nonneg _) hZ) hE _ lo hlo hgap
  intro M hM
  calc
    _ ≤ (S.card : ℝ) * (Z * (∏ h, lo h)⁻¹) *
        constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M :=
      constituentMatchingFamily_norm_le role size χ κ pivot n P hP Q childBound pivotBound
        ranges leaf hist hκ hhist root hroot M S lo hlo hcell
    _ ≤ (S.card : ℝ) * (Z * (∏ h, lo h)⁻¹) * E :=
      mul_le_mul_of_nonneg_left (henergy M hM) (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hZ (inv_nonneg.mpr (Finset.prod_nonneg fun h _ => (hlo h).le))))
    _ = _ := by ring

end
end Ostmann

end OAI
