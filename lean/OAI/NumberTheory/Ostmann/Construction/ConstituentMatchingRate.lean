import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingAverage
import OAI.NumberTheory.Ostmann.Construction.FixedPivotHYEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledRootIndex

namespace OAI

/-! # The sharp original-prior rate for actual matching families -/

namespace Ostmann
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituent_matching_family_square_rate {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ j, Fin (size j)) → ∀ q : ℕ, DirichletCharacter ℂ q)
    (κ : (Σ j, Fin (size j)) → ℕ → ℂ) (pivot : ℕ → (Σ j, Fin (size j)))
    (hκ : ∀ j q, ‖κ j q‖ ≤ 1)
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
      ∀ hP : (∀ p ∈ P, p.Prime ∧ V n < p),
      0 < X → 1 < X * lo → Real.exp (Δ - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      (∀ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n,
        historyFrequencyModulus ((transferFrequencyRange (V n)).erase 0) n n t ≤ 2 ^ h) →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      ∀ S : Finset (Equiv.Perm (CopyScheduleH (fun j : Σ a, Fin (size a) => role j.1) n)),
      ∀ lower : CopyScheduleH (fun j : Σ a, Fin (size a) => role j.1) n → ℝ,
      (∀ h, 0 < lower h) →
      (∀ h q, q ∈ cells (copyScheduleOrigin n h.val) → lower h ≤ (q : ℝ)) →
      ‖∑ u : CopyScheduleY (fun j : Σ a, Fin (size a) => role j.1) n → P,
        ((∏ y, primeSubsetPrior P (cells (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
        ∑ e ∈ S, ∑ d : ScheduledFrequencyIndex V n, ∑ d' : ScheduledFrequencyIndex V n,
          if frequencyRoot n (scheduledFrequencyHistory V n d) =
              frequencyRoot n (scheduledFrequencyHistory V n d') then
            ∑ l : CopyScheduleH (fun j : Σ a, Fin (size a) => role j.1) n → P,
              constituentCharacterCoefficient role size χ κ pivot n P (fun q hq => (hP q hq).1) cells
                childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
                (scheduledFrequencyHistory V n) u M (l, d) *
              conj (constituentCharacterCoefficient role size χ κ pivot n P (fun q hq => (hP q hq).1) cells
                childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
                (scheduledFrequencyHistory V n) u M (l ∘ e.symm, d')) else 0‖ ≤
        (S.card : ℝ) * ((∏ h : CopyScheduleH (fun j : Σ a, Fin (size a) => role j.1) n,
          (∑ q ∈ cells (copyScheduleOrigin n h.val), (q : ℝ)⁻¹)⁻¹) * (∏ h, lower h)⁻¹) *
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [constituent_fixedPivot_HY_square_rate role size childBound pivotBound ranges
    i hi n hu p hp hunique ψ C₀ K C ε hC hε hψ] with m hm
  intro V Δ X lo upper M P cells hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
    S lower hlower hlowerCell
  have he := hm V Δ X lo upper M P cells hV hN hV₀ hP hX hXlo hlo hsub hmass
    h J hsmall hrange a C₁ L ha hL hcell hJ
  dsimp only at he
  simp only [enumeratedPartitionEquiv_rest, Sum.elim_inl, Sum.elim_inr] at he
  have hb := constituent_matching_family_energy_bound role size χ κ pivot hκ n P
    (fun q hq => (hP q hq).1) cells childBound pivotBound ranges
    (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V n)
    (scheduledFrequencyHistory_injective V n) (scheduledRootIndex V n)
    (fun d d' h => (scheduledRootIndex_eq_iff V n d d').mp h) M S lower hlower hlowerCell
  simp only [scheduledRootIndex_eq_iff] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left ?_ ?_
  · convert he using 1
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (Finset.prod_nonneg (fun _ _ => by positivity))
      (inv_nonneg.mpr (Finset.prod_nonneg (fun h _ => (hlower h).le))))

end Ostmann

end OAI
