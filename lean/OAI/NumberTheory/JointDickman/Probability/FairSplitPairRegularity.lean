import OAI.NumberTheory.JointDickman.Probability.RemainingSplitRegularity

namespace OAI

/-! # The two remaining subsets in the amplification model -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem fairSelectedRemainingMass_nonneg {P A R : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hR : R ⊆ P) :
    0 ≤ fairSelectedRemainingMass P A R := by
  unfold fairSelectedRemainingMass
  split_ifs
  · apply mul_nonneg _ (by positivity)
    apply bernoulliSubsetMass_nonneg (union_subset hA hR)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  · exact le_rfl

theorem fairSelectedRemainingMass_sum {P A : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    (∑ R ∈ P.powerset, fairSelectedRemainingMass P A R) =
      bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A := by
  calc
    _ = ∑ R ∈ P.powerset,
        bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
          bernoulliSubsetMass P (remainingPrimeParameter A) R := by
      apply sum_congr rfl
      intro R hR
      exact fairSelectedRemainingMass_factor hP hA (mem_powerset.mp hR)
    _ = _ := by rw [← mul_sum, bernoulliSubsetMass_sum, mul_one]

open Classical in
noncomputable def fairRemainingPairFailure (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ) : ℝ :=
  ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
    if RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q then 0 else
      fairSelectedRemainingMass (auxiliaryPrimes B) A R *
        fairSelectedRemainingMass (auxiliaryPrimes B) D Q

open Classical in
theorem fairRemainingPairFailure_union (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    fairRemainingPairFailure B L τ C A D ≤
      (∑ R ∈ (auxiliaryPrimes B).powerset,
        if RegularPrimeSet B L τ C R then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) A R) *
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D +
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
        (∑ Q ∈ (auxiliaryPrimes B).powerset,
          if RegularPrimeSet B L τ C Q then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) D Q) := by
  classical
  have hP : ∀ p ∈ auxiliaryPrimes B, p.Prime := auxiliaryPrimes_prime B
  rw [← fairSelectedRemainingMass_sum hP hD, ← fairSelectedRemainingMass_sum hP hA,
    sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  unfold fairRemainingPairFailure
  apply sum_le_sum
  intro R hR
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro Q hQ
  have hx := fairSelectedRemainingMass_nonneg hP hA (mem_powerset.mp hR)
  have hy := fairSelectedRemainingMass_nonneg hP hD (mem_powerset.mp hQ)
  by_cases hr : RegularPrimeSet B L τ C R <;> by_cases hq : RegularPrimeSet B L τ C Q
  all_goals simp only [hr, hq, and_self, and_true, and_false, ite_true, ite_false,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals nlinarith only [mul_nonneg hx hy]

/-- Uniformly in the two selected coefficients, the two remaining subsets
lose at most the selected marginal mass times the regularity error. -/
theorem fair_remaining_pair_regularity_loss
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (A D : Finset ℕ) (C : ℝ), 0 ≤ C →
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
          (∏ p ∈ D, p : ℕ) ≤ Real.exp (κ * B) →
          fairRemainingPairFailure B L τ C A D ≤
            (bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D) *
                K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := fair_selected_remaining_regularity_loss hM hκ
  refine ⟨2 * K, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hevent] with B hb
  intro A D C hC hA hD ha hd
  have hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ (1 / 2 : ℝ) / p ∧ (1 / 2 : ℝ) / p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hA0 := bernoulliSubsetMass_nonneg hA hq
  have hD0 := bernoulliSubsetMass_nonneg hD hq
  have ha' := mul_le_mul_of_nonneg_right (hb A C hC hA ha) hD0
  have hd' := mul_le_mul_of_nonneg_left (hb D C hC hD hd) hA0
  have hu := fairRemainingPairFailure_union B L τ C hA hD
  nlinarith only [hu, ha', hd']

end JointDickman

end OAI
