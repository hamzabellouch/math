import OAI.NumberTheory.Ostmann.Construction.NaturalFixedPivotEnergy
import OAI.NumberTheory.Ostmann.Construction.UniformFixedPivotHistoryEnergy

namespace OAI

/-! # The actual rounded character cutoff in the fixed-pivot energy -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem uniform_constituent_natural_history_energy (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p)
      (X lo upper : ℝ) (M : ℕ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ),
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
  filter_upwards [uniform_constituent_natural_fixedPivot_energy n ψ C₀ K d ε hd hε hψ]
    with m hm
  intro I instI role size childBound pivotBound ranges i hi hu p hp hunique X lo upper M P cells
    hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have he := hm role size childBound pivotBound ranges i hi hu X lo upper M P cells
    hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have hf := constituent_fixedPivot_prior_fubini role size n M p hp hunique P
    (fun j => primeSubsetPrior P (cells (copyScheduleOrigin n j.val)))
    (fun j => primeSubsetPrior_mass P _ (hsub _) (hmass _))
    (fun t v => ‖fullAtomTransferWeight role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo upper) n v
      (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n t)‖ ^ 2)
  have hbound := (le_of_eq hf.symm).trans he
  simp only [enumeratedPartitionEquiv_rest, Sum.elim_inl, Sum.elim_inr] at hbound
  apply le_trans (le_of_eq ?_) hbound
  unfold constituentHistoryEnergy
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

end Ostmann

end OAI
