import OAI.NumberTheory.Ostmann.Construction.UniformFixedPivotHistoryEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorDiagonalBound
import OAI.NumberTheory.Ostmann.Construction.ScheduledRootIndex

namespace OAI

/-! # The code-preserving diagonal from actual selected-prime energy data -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem uniform_scheduled_anchor_energy_bound (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ M : ℝ in atTop,
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ a, Fin (size a)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ a, Fin (size a)) → ℕ → ℂ) (pivot : ℕ → (Σ a, Fin (size a)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p)
      (m : ℕ) (word : Fin m ≃ {i : Σ a, Fin (size a) // role i.1 = .word})
      (V : ℕ → ℕ) (Δ X lo upper : ℝ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
      (_hV : Monotone V) (_hN : (V n : ℝ) ≤ Real.exp (C * M))
      (_hV₀ : (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt M))
      (hP : ∀ p ∈ P, p.Prime ∧ V n < p)
      (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (Δ - C₀) ≤ lo)
      (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, 0 < ∑ p ∈ cells j, (p : ℝ)⁻¹)
      (h J : ℕ)
      (_hsmall : ∀ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n,
        historyFrequencyModulus ((transferFrequencyRange (V n)).erase 0) n n t ≤ 2 ^ h)
      (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ L z : ℝ) (_ha : 0 < a) (_hL : 1 ≤ L)
      (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (_hz : 0 < z) (_hm : (m : ℝ) ≤ z * L)
      (_hbulk : ∀ x, L ≤ ∑ p ∈ cells (copyScheduleOrigin n
        (scheduledBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m word x).val.val), (p : ℝ)⁻¹)
      (loH : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℝ)
      (_hloH : ∀ h, 0 < loH h)
      (_hlower : ∀ h p, p ∈ cells (copyScheduleOrigin n h.val) → loH h ≤ (p : ℝ))
      (A B : ℕ) (_hA : 0 < A) (gap : ℝ) (_hgap : Real.exp gap * (B : ℝ) ≤ ∏ h, loH h),
      (∑ N ∈ Finset.Icc A B,
        (constituentMatchingFamily role size χ κ pivot n P (fun p hp => (hP p hp).1) cells
          childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
          (scheduledFrequencyHistory V n)
          (scheduledAnchorMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m word) N).re) ≤
      Real.exp (-gap) *
        (Fintype.card (ScheduledNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n)).factorial *
        (∏ h : ScheduledNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ cells (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ) +
          ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M)) := by
  filter_upwards [uniform_constituent_history_energy n ψ C₀ K C ε hC hε hψ] with M hE
  intro I instI role size χ κ pivot hκ childBound pivotBound ranges i hi hu p hp hunique m word
    V Δ X lo upper P cells hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L z ha hL
    hcell hJ hz hm hbulk loH hloH hlower A B hA gap hgap
  apply scheduled_anchor_diagonal_bound role size χ κ pivot n m P (fun p hp => (hP p hp).1) cells
    childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V n)
    hκ (scheduledFrequencyHistory_injective V n) (scheduledRootIndex V n)
    (scheduledRootIndex_eq_iff V n) word loH hloH hlower A B hA gap
    ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M) L z
    hgap (lt_of_lt_of_le zero_lt_one hL) hz hm (fun _ => hmass _) hbulk
  intro N _
  exact hE role size childBound pivotBound ranges i hi hu p hp hunique V Δ X lo upper N P cells
    hV hN hV₀ hP hX hXlo hlo hsub (fun j => (hmass j).ne') h J hsmall hrange a C₁ L ha hL hcell hJ

end Ostmann

end OAI
