import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorNaturalEnergy
import OAI.NumberTheory.Ostmann.Characters.CharacterNonbulkBudget
import OAI.NumberTheory.Ostmann.Characters.CharacterDiagonalBudget

namespace OAI

/-! # The actual natural-cutoff anchor diagonal fits the character iteration -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_selected_natural_anchor_decay (n Bnb : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε c B B₁ C₁ a z : ℝ)
    (hd : 0 ≤ d) (hε : 0 < ε) (hc : 0 ≤ c) (ha : 0 < a)
    (hC₁ : 0 ≤ C₁) (hz : 1 ≤ z)
    (hbudget : 4 * c * Bnb ≤ z)
    (hB : 2 * B₁ + (C₁ + max (Real.log (3 / a)) 0 + ε) + Real.log 2 + 6 ≤ B)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) →
    let M := (m : ℝ)
    let V := naturalTransferCutoff (d * M) M
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ a, Fin (size a)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ a, Fin (size a)) → ℕ → ℂ) (pivot : ℕ → (Σ a, Fin (size a)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p)
      (bulk : Fin m ↪ (Σ a, Fin (size a)))
    (hrole : ∀ i, role (bulk i).1 = .word)
      (X lo upper : ℝ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
      (hP : ∀ p ∈ P, p.Prime ∧ V n < p)
      (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (d * M - C₀) ≤ lo)
      (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, 0 < ∑ p ∈ cells j, (p : ℝ)⁻¹)
      (h J : ℕ)
      (_hsmall : V n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h)
      (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (_hL : 1 ≤ L) (_hLM : L ≤ M)
      (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (_hm : (m : ℝ) ≤ z * L) (_hmlo : z * L / 2 ≤ (m : ℝ))
      (_hbulk : ∀ x, L ≤ ∑ p ∈ cells (copyScheduleOrigin n
        (selectedBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole x).val.val), (p : ℝ)⁻¹)
      (atomLo atomHi : I → ℕ) (_hranges : ranges = atomIntervalRanges role atomLo atomHi)
      (_hpositive : 0 < ∏ h : CopyScheduleH role n, (atomLo (copyScheduleOrigin n h.val) : ℝ))
      (A top : ℕ) (_hA : 0 < A) (gap : ℝ) (_hgap : Real.exp gap * (top : ℝ) ≤ ∏ h : CopyScheduleH role n, (atomLo (copyScheduleOrigin n h.val) : ℝ))
      (_hgaprate : (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * M ≤ gap)
      (_hcard : Nat.card {i : Σ a, Fin (size a) //
        i ∉ Set.range bulk ∧ role i.1 ≠ .outside} ≤ Bnb)
      (_hmassnb : ∀ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1)
        n m bulk hrole, Real.exp (-c * L) ≤
          ∑ p ∈ cells (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹),
      (∑ N ∈ Finset.Icc A top,
        (constituentMatchingFamily role size χ κ pivot n P (fun p hp => (hP p hp).1) cells
          childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
          (scheduledFrequencyHistory V n)
          (selectedAnchorMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole) N).re) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * M) := by
  obtain ⟨M₀, hM₀⟩ := (eventually_atTop.mp
    (uniform_selected_anchor_natural_energy n ψ C₀ K d ε hd hε hψ))
  refine ⟨M₀, ?_⟩
  filter_upwards [eventual_selected_nonbulk_cost n Bnb c 1 z hc (by norm_num)
    (lt_of_lt_of_le zero_lt_one hz) (by simpa only [one_mul] using hbudget)] with L hnb
  intro m hm₀ M V I instI role size χ κ pivot hκ childBound pivotBound ranges i hi hu p hp hunique
    bulk hrole X lo upper P cells hP hX hXlo hlo hsub hmass h J hsmall hrange hL hLM
    hcell hJ hm hmlo hbulk atomLo atomHi hranges hpositive A top hA gap hgap hgaprate hcard hmassnb
  have he := hM₀ M hm₀ role size χ κ pivot hκ childBound pivotBound ranges i hi hu p hp hunique
    m bulk hrole X lo upper P cells hP hX hXlo hlo hsub hmass h J hsmall hrange
    a C₁ L z ha hL hcell hJ (lt_of_lt_of_le zero_lt_one hz) hm hbulk
    atomLo atomHi hranges hpositive A top hA gap hgap
  have hn := hnb (fun i : Σ a, Fin (size a) => role i.1) m bulk hrole hmlo hcard
    (fun h => ∑ p ∈ cells (copyScheduleOrigin n h.val), (p : ℝ)⁻¹) hmassnb
  simp only [one_mul] at hn
  have hpow : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have henergy :
      (C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M ≤
        (C₁ + max (Real.log (3 / a)) 0 + ε) * (2 ^ n : ℕ) * M := by
    have hfirst := mul_le_mul_of_nonneg_left hLM
      (mul_nonneg (add_nonneg hC₁ (le_max_right (Real.log (3 / a)) 0)) (Nat.cast_nonneg (α := ℝ) (2 ^ n)))
    have hsecond := mul_le_mul_of_nonneg_left hpow (mul_nonneg hε.le (Nat.cast_nonneg m))
    change ε * M * 1 ≤ ε * M * (2 ^ n : ℕ) at hsecond
    nlinarith only [hfirst, hsecond]
  have hsmall := character_anchor_diagonal_small B B₁
    (C₁ + max (Real.log (3 / a)) 0 + ε) z M gap
    ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M)
    (selectedNonbulkCost (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole
      (fun h => ∑ p ∈ cells (copyScheduleOrigin n h.val), (p : ℝ)⁻¹))
    n hz (Nat.cast_nonneg m) hB hgaprate henergy hn
  exact he.trans (by simpa only [selectedNonbulkCost, Nat.cast_mul, mul_assoc] using hsmall)

end Ostmann

end OAI
