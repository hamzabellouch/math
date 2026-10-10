import OAI.NumberTheory.JointDickman.Amplification.ConditionalAdditionProduct

namespace OAI

/-! # Solving the second ratio condition for either addition product -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem ratio_log_bounds {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T)
    (hlo : T * c ≤ a) (hhi : a ≤ 2 * (T * c)) :
    0 ≤ Real.log a - Real.log T - Real.log c ∧
      Real.log a - Real.log T - Real.log c ≤ Real.log 2 := by
  have hl := Real.log_le_log (mul_pos hT hc) hlo
  have hu := Real.log_le_log ha hhi
  rw [Real.log_mul hT.ne' hc.ne'] at hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_pos hT hc).ne',
    Real.log_mul hT.ne' hc.ne'] at hu
  constructor <;> linarith only [hl, hu]

theorem first_addition_log_window {a c T u v : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) (hu : 0 < u) (hv : 0 < v)
    (hlo : T * (c * v) ≤ a * u) (hhi : a * u ≤ 2 * (T * (c * v))) :
    let t := Real.log T + Real.log c + Real.log v - Real.log a
    t ≤ Real.log u ∧ Real.log u ≤ t + Real.log 2 := by
  obtain ⟨hl, hh⟩ := ratio_log_bounds (mul_pos ha hu) (mul_pos hc hv) hT hlo hhi
  rw [Real.log_mul ha.ne' hu.ne', Real.log_mul hc.ne' hv.ne'] at hl hh
  dsimp only
  constructor <;> linarith only [hl, hh]

theorem second_addition_log_window {a c T u v : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) (hu : 0 < u) (hv : 0 < v)
    (hlo : T * (c * v) ≤ a * u) (hhi : a * u ≤ 2 * (T * (c * v))) :
    let t := Real.log a + Real.log u - Real.log T - Real.log c - Real.log 2
    t ≤ Real.log v ∧ Real.log v ≤ t + Real.log 2 := by
  obtain ⟨hl, hh⟩ := ratio_log_bounds (mul_pos ha hu) (mul_pos hc hv) hT hlo hhi
  rw [Real.log_mul ha.ne' hu.ne', Real.log_mul hc.ne' hv.ne'] at hl hh
  dsimp only
  constructor <;> linarith only [hl, hh]

open Classical in
noncomputable def firstAdditionRatioMass (B : ℕ) (A D : Finset ℕ) (Y T a c : ℝ) : ℝ :=
  ∑ V ∈ (additionPrimes B Y).powerset,
    bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter D) V *
      ∑ U ∈ (additionPrimes B Y).powerset,
        if T * (c * (∏ p ∈ V, p : ℕ)) ≤ a * (∏ p ∈ U, p : ℕ) ∧
            a * (∏ p ∈ U, p : ℕ) ≤ 2 * (T * (c * (∏ p ∈ V, p : ℕ))) ∧
            Y / 2 ≤ Real.log (∏ p ∈ U, p : ℕ) then
          bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter A) U else 0

/-- Uniformly in both retained coefficient products, an oriented second-ratio
event has conditional mass O(1/Y). -/
theorem first_addition_ratio_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (A D : Finset ℕ) (Y T a c : ℝ),
      A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B → 0 < T → 0 < a → 0 < c →
      firstAdditionRatioMass B A D Y T a c ≤ K / Y := by
  classical
  obtain ⟨K, hK, hbound⟩ := conditional_addition_small_ball hFord hM
    (κ := κ) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with B hb
  intro A D Y T a c hA hsize hY hYB hT ha hc
  have hmass (E : Finset ℕ) (hE : E ⊆ additionPrimes B Y) (F : Finset ℕ) :
      0 ≤ bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter F) E :=
    bernoulliSubsetMass_nonneg hE (fun p hp =>
      conditionalAdditionParameter_bounds F (additionPrimes_prime B Y p hp).two_le)
  have hp (E : Finset ℕ) (hE : E ⊆ additionPrimes B Y) : (0 : ℝ) < (∏ p ∈ E, p : ℕ) := by
    exact_mod_cast prod_pos (fun p hpe => (additionPrimes_prime B Y p (hE hpe)).pos)
  unfold firstAdditionRatioMass
  calc
    _ ≤ ∑ V ∈ (additionPrimes B Y).powerset,
        bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter D) V * (K / Y) := by
      apply sum_le_sum
      intro V hV
      apply mul_le_mul_of_nonneg_left _ (hmass V (mem_powerset.mp hV) D)
      let t := Real.log T + Real.log c + Real.log (∏ p ∈ V, p : ℕ) - Real.log a
      refine le_trans ?_ (hb A Y t hA hsize hY hYB)
      unfold conditionalAdditionLogIntervalMass
      apply sum_le_sum
      intro U hU
      have hU0 := hp U (mem_powerset.mp hU)
      have hV0 := hp V (mem_powerset.mp hV)
      split_ifs with he hwindow
      · exact le_rfl
      · obtain ⟨hl, hh⟩ := first_addition_log_window ha hc hT hU0 hV0 he.1 he.2.1
        exact False.elim (hwindow ⟨hl, hh, he.2.2⟩)
      · exact hmass U (mem_powerset.mp hU) A
      · exact le_rfl
    _ = K / Y := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

end JointDickman

end OAI
