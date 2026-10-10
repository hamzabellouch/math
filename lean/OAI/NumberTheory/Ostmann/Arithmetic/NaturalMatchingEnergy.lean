import OAI.NumberTheory.Ostmann.Construction.ConstituentEnergyMarginal
import OAI.NumberTheory.Ostmann.Construction.NaturalFixedPivotEnergy

namespace OAI

/-! # The literal diagonal history energy at the rounded cutoffs -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem uniform_natural_constituentHistoryEnergy_bound (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
      ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (size : I → ℕ)
        (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
        (pivot : I) (_hpivot : role pivot = .pivot n)
        (_hunique : ∀ j, role j = .pivot n → j = pivot),
      ∀ X lo upper : ℝ, ∀ M : ℕ,
      ∀ P : Finset ℕ, ∀ cells : (Σ a, Fin (size a)) → Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ naturalTransferCutoff (d * m) m n < p) →
      0 < X → 1 < X * lo → Real.exp (d * m - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      naturalTransferCutoff (d * m) m n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      constituentHistoryEnergy role size n P cells childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper)
        (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n) M ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [uniform_constituent_natural_fixedPivot_energy n ψ C₀ K d ε hd hε hψ] with m hm
  intro I instI role size childBound pivotBound ranges i hi hu pivot hpivot hunique X lo upper M P cells hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  rw [constituentHistoryEnergy_eq_fixedPivot role size n M P cells hsub hmass
    pivot hpivot hunique]
  exact hm role size childBound pivotBound ranges i hi hu X lo upper M P cells hP hX hXlo hlo hsub hmass h J hsmall hrange
    a C₁ L ha hL hcell hJ

theorem natural_constituentHistoryEnergy_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (pivot : I) (hpivot : role pivot = .pivot n)
    (hunique : ∀ j, role j = .pivot n → j = pivot)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop, ∀ X lo upper : ℝ, ∀ M : ℕ,
      ∀ P : Finset ℕ, ∀ cells : (Σ a, Fin (size a)) → Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ naturalTransferCutoff (d * m) m n < p) →
      0 < X → 1 < X * lo → Real.exp (d * m - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      naturalTransferCutoff (d * m) m n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      constituentHistoryEnergy role size n P cells childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper)
        (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n) M ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [uniform_natural_constituentHistoryEnergy_bound n ψ C₀ K d ε hd hε hψ]
    with m hm
  exact hm role size childBound pivotBound ranges i hi hu pivot hpivot hunique

end Ostmann

end OAI
