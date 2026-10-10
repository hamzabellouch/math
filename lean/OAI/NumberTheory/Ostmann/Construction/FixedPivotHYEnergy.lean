import OAI.NumberTheory.Ostmann.Construction.FixedPivotScheduledEnergy

namespace OAI

/-! # Sharp history energy under the literal H and Y prime priors -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem constituent_fixedPivot_HY_square_rate {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (p : I) (hp : role p = .pivot n) (hunique : ∀ j, role j = .pivot n → j = p)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop, ∀ V : ℕ → ℕ, ∀ Δ X lo upper : ℝ, ∀ M : ℕ,
      ∀ P : Finset ℕ, ∀ cells : (Σ a, Fin (size a)) → Finset ℕ,
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
      (let e := pivotConstituentEquiv role size n p hp hunique
       let ρ := fun j : Σ a, Fin (size a) => role j.1
       let μ := fun j : SurvivingConstituent role size n =>
         primeSubsetPrior P (cells (copyScheduleOrigin n j.val))
       ∑ u : CopyScheduleY ρ n → P,
         (∏ y, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inr y))) (u y)) *
         ∑ l : CopyScheduleH ρ n → P,
           (∏ h, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inl h))) (l h)) *
           ∑ d : ScheduledFrequencyIndex V n,
             ‖fullAtomTransferWeight role childBound pivotBound ranges
               (scheduleFourierLeaf role ψ X lo upper) n
               (scheduledInsertedAtoms role n M
                 (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
                 (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)))
               (scheduledFrequencyHistory V n d)‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [constituent_fixedPivot_scheduled_square_rate role size childBound pivotBound
    ranges i hi n hu ψ C₀ K C ε hC hε hψ] with m hm
  intro V Δ X lo upper M P cells hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have he := hm V Δ X lo upper M P cells hV hN hV₀ hP hX hXlo hlo hsub hmass
    h J hsmall hrange a C₁ L ha hL hcell hJ
  have hf := constituent_fixedPivot_prior_fubini role size n M p hp hunique P
    (fun j => primeSubsetPrior P (cells (copyScheduleOrigin n j.val)))
    (fun j => primeSubsetPrior_mass P _ (hsub _) (hmass _))
    (fun d v => ‖fullAtomTransferWeight role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo upper) n v (scheduledFrequencyHistory V n d)‖ ^ 2)
  exact le_trans (le_of_eq hf.symm) he

end Ostmann

end OAI
