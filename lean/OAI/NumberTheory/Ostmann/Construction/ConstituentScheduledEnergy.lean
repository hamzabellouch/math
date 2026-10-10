import OAI.NumberTheory.Ostmann.Construction.ConstituentEnergyTransport
import OAI.NumberTheory.Ostmann.Construction.ScheduledSampledEnergy

namespace OAI

/-! # Original-prior energy for the actual varying-cutoff constituent schedule -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem constituent_scheduled_square_rate {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop, ∀ V : ℕ → ℕ, ∀ Δ X lo upper : ℝ,
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
      (∑ d : ScheduledFrequencyIndex V n, ∑ q : SurvivingConstituent role size n → P,
        scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
          (fun j => primeSubsetPrior P (cells j)) q *
          ‖fullAtomTransferWeight role childBound pivotBound ranges
            (scheduleFourierLeaf role ψ X lo upper) n
            (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)
            (scheduledFrequencyHistory V n d)‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [scheduled_clipped_square_rate role childBound pivotBound ranges i.1 hi n hu
    ψ C₀ K C ε hC hε hψ] with m hm
  intro V Δ X lo upper P cells hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  let S := (transferFrequencyRange (V n)).erase 0
  have hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V n := by
    intro s hs
    exact ⟨(Finset.mem_erase.mp hs).1,
      (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2⟩
  have he := scheduled_full_fourier_energy_le role childBound pivotBound ranges ψ X lo upper
    hX hXlo V hV n
    (fun q : SurvivingConstituent role size n → P =>
      scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
        (fun j => primeSubsetPrior P (cells j)) q)
    (fun q => Finset.prod_nonneg fun _ _ => primeSubsetPrior_nonneg _ _ _)
    (fun q a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)
  apply he.trans
  apply constituent_energy_transport role size i hi n P cells hsub hmass
    (fun t base => ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper
      S (V 0) n base t‖ ^ 2)
  intro base
  exact hm (V n) (V 0) Δ X lo upper P S hN hV₀ hS hP hX hlo
    (cells i) h J hsmall hrange a C₁ L ha hL hcell hJ base

end Ostmann

end OAI
