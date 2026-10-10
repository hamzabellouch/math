import OAI.NumberTheory.JointDickman.Amplification.AmplificationRegularityIdentity
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! # The unpartitioned signed regularity error in the amplification argument -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem dyadicBoxIndices_card_bound {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlog : Real.log T ≤ (B : ℝ)/10) :
    ((dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card : ℝ) ≤ 5*B := by
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnon : 0 ≤ (2*(B : ℝ)+Real.log T)/Real.log 2 :=
    div_nonneg (by linarith [Real.log_nonneg hT]) (by linarith)
  have hceil := Nat.ceil_lt_add_one hnon
  have hfrac : (2*(B : ℝ)+Real.log T)/Real.log 2 ≤ (21/5 : ℝ)*B := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith
  have hU : (dyadicBoxUpper B T : ℝ) ≤ 5*B := by
    simp only [dyadicBoxUpper,Nat.cast_add,Nat.cast_one]
    linarith
  have hcard : (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card ≤
      dyadicBoxUpper B T := by
    unfold dyadicBoxIndices
    exact card_image_le.trans (by rw [Nat.card_Ico]; exact Nat.sub_le _ _)
  exact (by exact_mod_cast hcard :
    ((dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card : ℝ) ≤
      dyadicBoxUpper B T).trans hU

open Classical in
/-- The published sieve input controls the entire signed smooth regularity
loss; the dyadic number of boxes cancels the local factor 1/B. -/
theorem amplification_signed_regularity_loss
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
          (∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
            discardedAmplificationTerm B L j τ C T g h c b a) ≤
            K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hbox⟩ := dyadicBox_signed_regularity_loss hFord hM
  refine ⟨5*K,by positivity,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hbox⟩ := hbox L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hbox,eventually_ge_atTop 30] with B hb hB
  intro T hT hlog C j U V hC hj hU hV g h hg hh
  rw [discarded_amplification_dyadic_identity hB hT hlog L j U V τ C g h hU hV]
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hA0 : 0 ≤ K/((B : ℝ)*T)*singularFactor 24 j*
      (ε B+Real.exp (-(1/10 : ℝ)*C)) := by
    apply mul_nonneg
    · exact mul_nonneg (by positivity)
        (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    · exact add_nonneg (hε0 B) (Real.exp_pos _).le
  calc
    _ ≤ ∑ _k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
      apply sum_le_sum
      intro k hk
      exact hb T hT hlog k hk C j hC hj g h hg hh
    _ = ((dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card : ℝ)*
        (K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C))) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ (5*(B : ℝ))*(K/((B : ℝ)*T)*singularFactor 24 j*
        (ε B+Real.exp (-(1/10 : ℝ)*C))) :=
      mul_le_mul_of_nonneg_right (dyadicBoxIndices_card_bound hB hT hlog) hA0
    _ = _ := by field_simp

end JointDickman

end OAI
