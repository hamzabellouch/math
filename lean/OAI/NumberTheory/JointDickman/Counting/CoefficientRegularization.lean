import OAI.NumberTheory.JointDickman.Amplification.AmplificationRegularityLoss

namespace OAI

/-! # Removing all three coefficient regularity cutoffs from the signed sum -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def regularizedAmplificationArithmeticSum (B L j : ℕ) (τ C T : ℝ)
    (U V : ℕ) (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    if coefficientTripleRegular B L τ C a b c then
      amplificationArithmeticTerm B j T g h c b a else 0

open Classical in
theorem amplification_regularization_error (B L j : ℕ) (τ C T : ℝ) (U V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    |amplificationArithmeticSum B j T U V g h-
        regularizedAmplificationArithmeticSum B L j τ C T U V g h| ≤
      ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        discardedAmplificationTerm B L j τ C T g h c b a := by
  unfold amplificationArithmeticSum regularizedAmplificationArithmeticSum
  simp_rw [mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro c _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro b _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a _
  unfold discardedAmplificationTerm
  split_ifs <;> simp

open Classical in
/-- The three coefficient regularity restrictions cost the published
vanishing error plus the explicit tail, uniformly for bounded site tests. -/
theorem amplification_coefficient_regularization
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 →
          ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → j ≠ 0 →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |amplificationArithmeticSum B j T U V g h-
            regularizedAmplificationArithmeticSum B L j τ C T U V g h| ≤
            K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hloss⟩ := amplification_signed_regularity_loss hFord hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss] with B hb
  intro T hT hlog C j U V hC hj hU hV g h hg hh
  exact (amplification_regularization_error B L j τ C T U V g h).trans
    (hb T hT hlog C j U V hC hj hU hV g h hg hh)

end JointDickman

end OAI
