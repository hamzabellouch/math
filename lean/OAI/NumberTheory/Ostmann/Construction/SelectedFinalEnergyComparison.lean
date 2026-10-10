import OAI.NumberTheory.Ostmann.Construction.UniformConstituentEnergy
import OAI.NumberTheory.Ostmann.Construction.ConstituentSelectedFinalSymmetrization
import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyBounds
import OAI.NumberTheory.Ostmann.Construction.ScheduledRootIndex

namespace OAI

/-! # Final comparison with the actual selected-prime energy -/
namespace Ostmann
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_final_energy_comparison (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ M : ℝ in atTop,
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (pivot : ℕ → (Σ i, Fin (size i)))
      (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
      (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, role (bulk i).1 = .word)
      (V : ℕ → ℕ) (_hV : Monotone V)
      (Δ X lo upper : ℝ) (_hN : (V (n + 1) : ℝ) ≤ Real.exp (C * M))
      (_hV₀ : (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt M))
      (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ V (n + 1) < p)
      (cells : (Σ a, Fin (size a)) → Finset ℕ)
      (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (Δ - C₀) ≤ lo)
      (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
      (h J : ℕ)
      (_hsmall : ∀ t : FrequencyTree ((transferFrequencyRange (V (n + 1))).erase 0) (n + 1),
        historyFrequencyModulus ((transferFrequencyRange (V (n + 1))).erase 0) (n + 1) (n + 1) t ≤ 2 ^ h)
      (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ L : ℝ) (_ha : 0 < a) (_hL : 1 ≤ L)
      (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (center : ∀ p : ℕ, ZMod p) (E : ℝ) (_hE : 0 ≤ E)
      (_hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
        ∀ d d' : ScheduledFrequencyIndex V (n + 1), scheduledRootIndex V (n + 1) d = scheduledRootIndex V (n + 1) d' →
        ‖∑ q : SurvivingConstituent role size (n + 1) → P,
          ((∏ i, primeSubsetPrior P (cells (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
          (constituentPrimeTerm role size χ κ pivot (n + 1) P (fun p hp => (hP p hp).1)
            childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) center
            (scheduledFrequencyHistory V (n + 1) d) q *
          conj (constituentPrimeTerm role size χ κ pivot (n + 1) P (fun p hp => (hP p hp).1)
            childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) center
            (scheduledFrequencyHistory V (n + 1) d')
            (fun i => q (selectedFinalRelativePerm (fun i : Σ a, Fin (size a) => role i.1) n m bulk hbulk e f i))))‖ ≤ E),
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P
        (fun p hp => (hP p hp).1) cells childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V (n + 1)) center‖ ^ 2 ≤
      ((transferFrequencyRange (V (n + 1))).card : ℝ) *
        (Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ (n + 1) : ℕ) * L + ε * M) /
          (Fintype.card (FinalParityReassignments n m) : ℝ) +
        (Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 * E) := by
  filter_upwards [uniform_constituent_scheduled_square_rate (n + 1) ψ C₀ K C ε hC hε hψ]
    with M hM
  intro I instI role size χ κ hκ pivot childBound pivotBound ranges i hi hu m bulk hbulk
    V hV Δ X lo upper hN hV₀ P hP cells hX hXlo hlo hsub hmass h J hsmall hrange
    a C₁ L ha hL hcell hJ center E hE hpair
  have henergy := hM role size childBound pivotBound ranges i hi hu V Δ X lo upper P cells
    hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have hcomp := constituent_selected_final_unique_comparison role size χ κ hκ pivot n m bulk hbulk P
    (fun p hp => (hP p hp).1) cells hsub hmass childBound pivotBound ranges
    (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V (n + 1))
    (scheduledFrequencyHistory_injective V (n + 1)) (scheduledRootIndex V (n + 1))
    (fun d d' hd => (scheduledRootIndex_eq_iff V (n + 1) d d').mp hd) center E hE hpair
  have hcard : (Fintype.card (FinalParityReassignments n m) : ℝ) =
      (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) := by
    rw [card_finalParityReassignments]
  rw [← hcard] at hcomp
  simp only [Fintype.card_coe] at hcomp
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact add_le_add (div_le_div_of_nonneg_right henergy (Nat.cast_nonneg _)) le_rfl

end Ostmann

end OAI
