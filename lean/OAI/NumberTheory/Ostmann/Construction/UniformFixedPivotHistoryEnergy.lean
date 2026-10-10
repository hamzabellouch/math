import OAI.NumberTheory.Ostmann.Construction.FixedPivotHYEnergy
import OAI.NumberTheory.Ostmann.Construction.ConstituentFamilyEnergy

namespace OAI

/-! # Uniform sharp energy for the actual externally fixed pivot histories -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem uniform_constituent_history_energy (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p),
    ∀ (V : ℕ → ℕ) (Δ X lo upper : ℝ) (M : ℕ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ),
      Monotone V → (V n : ℝ) ≤ Real.exp (C * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ p ∈ P, p.Prime ∧ V n < p) →
      0 < X → 1 < X * lo → Real.exp (Δ - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      (∀ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n,
        historyFrequencyModulus ((transferFrequencyRange (V n)).erase 0) n n t ≤ 2 ^ h) →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      constituentHistoryEnergy role size n P cells childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V n) M ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [uniform_constituent_fixedPivot_scheduled_square_rate n ψ C₀ K C ε hC hε hψ]
    with m hm
  intro I instI role size childBound pivotBound ranges i hi hu p hp hunique V Δ X lo upper M P cells
    hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have he := hm role size childBound pivotBound ranges i hi hu V Δ X lo upper M P cells
    hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have hf := constituent_fixedPivot_prior_fubini role size n M p hp hunique P
    (fun j => primeSubsetPrior P (cells (copyScheduleOrigin n j.val)))
    (fun j => primeSubsetPrior_mass P _ (hsub _) (hmass _))
    (fun d v => ‖fullAtomTransferWeight role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo upper) n v (scheduledFrequencyHistory V n d)‖ ^ 2)
  have h := (le_of_eq hf.symm).trans he
  simp only [enumeratedPartitionEquiv_rest, Sum.elim_inl, Sum.elim_inr] at h
  apply le_trans (le_of_eq ?_) h
  unfold constituentHistoryEnergy
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

end Ostmann

end OAI
