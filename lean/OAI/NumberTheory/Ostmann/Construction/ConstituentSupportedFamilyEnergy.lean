import OAI.NumberTheory.Ostmann.Construction.ConstituentFamilyEnergy
import OAI.NumberTheory.Ostmann.Construction.ConstituentSupportedMatchingAverage
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

theorem constituentMatchingFamily_norm_on_product {R : Type*} [Fintype R]
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (lower : ℝ) (hlower : 0 < lower)
    (hproduct : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
      (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ)) :
    ‖constituentMatchingFamily role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist S M‖ ≤
      (S.card : ℝ) * ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
        (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹) *
        constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M := by
  have h := constituent_matching_family_energy_on_product role size χ κ pivot hκ n P hP Q
    childBound pivotBound ranges leaf hist hhist root (fun d d' hd => (hroot d d').mp hd)
    M S lower hlower hproduct
  simpa only [constituentMatchingFamily, primeMatchingContribution, constituentHistoryEnergy, hroot, finite_univ_canonical] using h

theorem constituentMatchingFamily_interval_on_product {R : Type*} [Fintype R]
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (a b : ℕ) (ha : 0 < a) (gap E lower : ℝ) (hE : 0 ≤ E) (hlower : 0 < lower)
    (hgap : Real.exp gap * (b : ℝ) ≤ lower)
    (hproduct : ∀ M ∈ Finset.Icc a b, ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
      (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ))
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
    ((S.card : ℝ) * Z) E gap (mul_nonneg (Nat.cast_nonneg _) hZ) hE Unit (fun _ => lower) (fun _ => hlower) (by simpa using hgap)
  intro M hM
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]
  calc
    _ ≤ (S.card : ℝ) * (Z * lower⁻¹) *
        constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M :=
      constituentMatchingFamily_norm_on_product role size χ κ pivot n P hP Q childBound pivotBound
        ranges leaf hist hκ hhist root hroot M S lower hlower (hproduct M hM)
    _ ≤ (S.card : ℝ) * (Z * lower⁻¹) * E :=
      mul_le_mul_of_nonneg_left (henergy M hM) (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hZ (inv_nonneg.mpr hlower.le)))
    _ = _ := by ring

end
end Ostmann

end OAI
