import OAI.NumberTheory.Ostmann.Construction.UniformConstituentEnergy
import OAI.NumberTheory.Ostmann.Construction.RoundedEnergyCutoffs

namespace OAI

/-! # Fixed-pivot energy at the manuscript's actual rounded cutoffs -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem uniform_constituent_natural_square_rate (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
      ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (size : I → ℕ)
        (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b),
      ∀ X lo upper : ℝ,
      ∀ P : Finset ℕ, ∀ cells : (Σ a, Fin (size a)) → Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ naturalTransferCutoff (d * m) m n < p) →
      0 < X → 1 < X * lo → Real.exp (d * m - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      naturalTransferCutoff (d * m) m n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      (∑ j : ScheduledFrequencyIndex (naturalTransferCutoff (d * m) m) n,
        ∑ q : SurvivingConstituent role size n → P,
        scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
          (fun j => primeSubsetPrior P (cells j)) q *
          ‖fullAtomTransferWeight role childBound pivotBound ranges
            (scheduleFourierLeaf role ψ X lo upper) n
            (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)
            (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n j)‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  let C := (2 : ℝ) ^ n * d + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrate := uniform_constituent_scheduled_square_rate n
    ψ C₀ K C (ε / 4) hC (by positivity) hψ
  have hrate' := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).eventually hrate
  filter_upwards [hrate', eventual_rounded_frequency_card n d hd, eventually_ge_atTop (0 : ℝ)]
    with m hm hc hm0
  intro I instI role size childBound pivotBound ranges i hi hu X lo upper P cells hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  let V := naturalTransferCutoff (d * m) m
  have hV : Monotone V := naturalTransferCutoff_monotone _ _ (mul_nonneg hd hm0)
  have hN : (V n : ℝ) ≤ Real.exp (C * (4 * m)) := by
    have hn := hc n le_rfl
    have hnat : (V n : ℝ) ≤ ((transferFrequencyRange (V n)).card : ℝ) := by
      rw [card_transferFrequencyRange]
      push_cast
      linarith [show (0 : ℝ) ≤ (V n : ℝ) from Nat.cast_nonneg _]
    exact hnat.trans (hn.trans (Real.exp_le_exp.mpr (by
      change C * m ≤ C * (4 * m)
      have h4 : m ≤ 4 * m := by linarith
      exact mul_le_mul_of_nonneg_left h4 hC)))
  have hv0 : (V 0 : ℝ) ≤ Real.exp (d * m + Real.sqrt (4 * m)) := rounded_bottom_frequency_bound _ _
  have hmod (t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n) :
      historyFrequencyModulus ((transferFrequencyRange (V n)).erase 0) n n t ≤ 2 ^ h := by
    apply (historyFrequencyModulus_le _ (V n) _ n n t).trans hsmall
    intro s hs
    exact (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2
  have hb := hm role size childBound pivotBound ranges i hi hu V (d * m) X lo upper P cells hV hN hv0 hP hX hXlo hlo hsub hmass
    h J hmod hrange a C₁ L ha hL hcell hJ
  have he : ε / 4 * (4 * m) = ε * m := by ring
  simpa only [id_eq, he, V] using hb

end Ostmann

end OAI
