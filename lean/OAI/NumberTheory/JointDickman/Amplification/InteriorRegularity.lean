import OAI.NumberTheory.JointDickman.Amplification.InteriorAmplificationMass
import OAI.NumberTheory.JointDickman.Amplification.RegularAmplificationMass

namespace OAI

/-! # The interior positive mass survives all four regularity cutoffs -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def fairRegularInteriorMass (B L T : ℕ) (τ C : ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationInteriorPairs B T then
      fairRegularAmplificationAt B L τ C A D else 0

open Classical in
theorem fairFourSubsetFailureAt_nonneg (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    0 ≤ fairFourSubsetFailureAt B L τ C A D := by
  unfold fairFourSubsetFailureAt
  apply sum_nonneg
  intro R hR
  apply sum_nonneg
  intro Q hQ
  split_ifs
  · exact le_rfl
  · exact mul_nonneg
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hA (mem_powerset.mp hR))
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hD (mem_powerset.mp hQ))

open Classical in
theorem interior_mass_regular_loss {B L T : ℕ} (τ C : ℝ) (hB : 0 < B) (hT : 0 < T) :
    (∑ ac ∈ amplificationInteriorPairs B T,
      primeProductMass (auxiliaryPrimes B) (1/2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1/2) ac.2) ≤
      fairRegularInteriorMass B L T τ C + fairFourSubsetFailure B L T τ C := by
  rw [primeProductPair_sum_event]
  unfold fairRegularInteriorMass fairFourSubsetFailure
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro A hA
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro D hD
  have hfail := fairFourSubsetFailureAt_nonneg B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationInteriorPairs B T
  · have hp' := amplificationInteriorPairs_subset hB hT hp
    simp only [hp, hp', ite_true]
    exact (fairRegularAmplificationAt_complement B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)).symm.le
  · simp only [hp, ite_false, zero_add]
    split_ifs
    · exact hfail
    · exact le_rfl

theorem interior_regular_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        d ≤ (B : ℝ)*fairRegularInteriorMass B L T τ C := by
  obtain ⟨d,hd,hpositive⟩ := interior_amplification_first_moment_lower hSD hM hMP
  obtain ⟨K,hK,hloss⟩ := amplification_regularity_loss hFord hM
  refine ⟨d/2, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε,_,hε,hlarge⟩ := hloss L τ hL hτ
  let C₀ := max 0 (10*Real.log (4*K/d))
  have hC₀ : 0 ≤ C₀ := le_max_left _ _
  have htail : ∀ C : ℝ, C₀ ≤ C → K*Real.exp (-(1/10 : ℝ)*C) ≤ d/4 := by
    intro C hC
    have hlog : 10*Real.log (4*K/d) ≤ C := (le_max_right _ _).trans hC
    have harg : -(1/10 : ℝ)*C ≤ -Real.log (4*K/d) := by linarith only [hlog]
    calc
      _ ≤ K*Real.exp (-Real.log (4*K/d)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hK.le
      _ = d/4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 4*K/d)]
        field_simp
  refine ⟨C₀,hC₀,?_⟩
  have hsmall := hε.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d/(4*K)))
  filter_upwards [hpositive,hlarge,hsmall,eventually_gt_atTop 0] with B hp hl he hB
  intro C T hC hT hTsize
  have hpos := hp T hT hTsize
  have hlos := hl C T (hC₀.trans hC) hT hTsize
  have htails := htail C hC
  have heps : K*ε B ≤ d/4 := by
    have hh := mul_le_mul_of_nonneg_left he hK.le
    have heq : K*(d/(4*K)) = d/4 := by field_simp
    rwa [heq] at hh
  have hc := mul_le_mul_of_nonneg_left (interior_mass_regular_loss (L := L) τ C hB hT) (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  rw [mul_add] at hc
  nlinarith only [hpos,hlos,htails,heps,hc]

end JointDickman

end OAI
