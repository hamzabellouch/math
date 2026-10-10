import OAI.NumberTheory.Ostmann.Arithmetic.NaturalMatchingEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledBadDiagonalBound
import OAI.NumberTheory.Ostmann.Construction.ScheduledRootIndex

namespace OAI

/-! # The original-prior bad diagonal with its energy estimate discharged -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem natural_bad_diagonal_bound (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ t : ℝ in atTop, ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (size : I → ℕ)
        (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
        (piv : I) (_hpiv : role piv = .pivot n)
        (_hunique : ∀ j, role j = .pivot n → j = piv)
        (X lo upper : ℝ) (P : Finset ℕ) (Q : (Σ a, Fin (size a)) → Finset ℕ),
      ∀ hP : (∀ p ∈ P, p.Prime ∧ naturalTransferCutoff (d * t) t n < p),
      0 < X → 1 < X * lo → Real.exp (d * t - C₀) ≤ lo →
      (∀ j, Q j ⊆ P) → (∀ j, (∑ p ∈ Q j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      naturalTransferCutoff (d * t) t n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h →
      (∀ p ∈ Q i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      ∀ (χ : (Σ j, Fin (size j)) → ∀ p : ℕ, DirichletCharacter ℂ p)
        (κ : (Σ j, Fin (size j)) → ℕ → ℂ) (pivot : ℕ → (Σ j, Fin (size j))),
      (∀ j p, ‖κ j p‖ ≤ 1) →
      ∀ (m : ℕ) (word : Fin m ≃ {j : Σ a, Fin (size a) // role j.1 = .word}),
      0 < m →
      ∀ lower : CopyScheduleH (fun j : Σ a, Fin (size a) => role j.1) n → ℝ,
      (∀ h, 0 < lower h) →
      (∀ h p, p ∈ Q (copyScheduleOrigin n h.val) → lower h ≤ (p : ℝ)) →
      ∀ A B : ℕ, 0 < A → ∀ gap Lb z : ℝ,
      Real.exp gap * (B : ℝ) ≤ ∏ h, lower h → 0 < Lb → 0 < z →
      (m : ℝ) ≤ z * Lb →
      (∀ x, Lb ≤ ∑ p ∈ Q (copyScheduleOrigin n
        (scheduledBulkCoordinates (fun j : Σ a, Fin (size a) => role j.1) n m word x).val.val),
          (p : ℝ)⁻¹) →
      (∑ M ∈ Finset.Icc A B,
        (constituentMatchingFamily role size χ κ pivot n P (fun p hp => (hP p hp).1) Q
          childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
          (scheduledFrequencyHistory (naturalTransferCutoff (d * t) t) n)
          (scheduledDiagonalBadMatchingSet (fun j : Σ a, Fin (size a) => role j.1) n m word) M).re) ≤
        Real.exp (-gap) *
          (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
          (Fintype.card (ScheduledNonbulkH (fun j : Σ a, Fin (size a) => role j.1) n)).factorial *
          (∏ h : ScheduledNonbulkH (fun j : Σ a, Fin (size a) => role j.1) n,
            (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp ((Real.log z + Real.log (2 ^ n : ℕ) / 4 + 2) * (2 ^ n * m : ℕ) +
            ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * t)) := by
  filter_upwards [uniform_natural_constituentHistoryEnergy_bound n ψ C₀ K d ε hd hε hψ]
    with t ht
  intro I instI role size childBound pivotBound ranges i hi hu piv hpiv hunique X lo upper P Q hP
    hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ χ κ pivot hκ m word hm
    lower hlower hlowerCell A B hA gap Lb z hgap hLb hz hmLb hbulk
  let V := naturalTransferCutoff (d * t) t
  have hmassH (h : CopyScheduleH (fun j : Σ a, Fin (size a) => role j.1) n) :
      0 < ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹ := by
    have hn : 0 ≤ ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹ :=
      Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    exact lt_of_le_of_ne hn (Ne.symm (hmass _))
  refine scheduled_bad_diagonal_bound role size χ κ pivot n m P (fun p hp => (hP p hp).1) Q
    childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
    (scheduledFrequencyHistory V n) hκ (scheduledFrequencyHistory_injective V n)
    (scheduledRootIndex V n) (scheduledRootIndex_eq_iff V n) word hm lower hlower hlowerCell
    A B hA gap ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * t)
    Lb z hgap hLb hz hmLb hmassH hbulk ?_
  intro M _
  exact ht role size childBound pivotBound ranges i hi hu piv hpiv hunique X lo upper M P Q
    hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ

end Ostmann

end OAI
