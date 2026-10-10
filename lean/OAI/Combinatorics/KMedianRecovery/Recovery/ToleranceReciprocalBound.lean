import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DyadicExponent

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

lemma tolerance_reciprocal_bound {epsilon : ℝ} (he : 0 < epsilon) :
    1/tolerance epsilon ≤ 8/epsilon + 16 := by
  have hx : (1:ℝ) ≤ max (4/epsilon) 8 := le_trans (by norm_num) (le_max_right _ _)
  have hhi := (dyadic_round_bounds hx).2
  have hmax : max (4/epsilon) (8:ℝ) ≤ 4/epsilon+8 := by
    have hp : 0 ≤ (4:ℝ)/epsilon := by positivity
    apply max_le <;> linarith
  unfold tolerance
  rw [one_div_one_div]
  calc
    _ ≤ 2*max (4/epsilon) 8 := hhi.le
    _ ≤ 2*(4/epsilon+8) := mul_le_mul_of_nonneg_left hmax (by norm_num)
    _ = 8/epsilon + 16 := by ring

lemma sampledCategorical_bit_bound {E : Type*} [Fintype E] {a : ℕ} {epsilon : ℝ}
    (hq : 0 < Fintype.card E) (ha : 0 < a) (he : 0 < epsilon) :
    (Fintype.card (BinaryOracleIndex E a (stepExponent a epsilon)
      (sampleCount (Fintype.card E) a epsilon)) : ℝ) ≤
      ((2*(a:ℝ)^2*(8/epsilon+16)) * Fintype.card E *
        ((Fintype.card E:ℝ)*(a:ℝ)^4*(8/epsilon+16)^4+1) * a + a) *
        (2*(a:ℝ)^2*(8/epsilon+16)) := by
  have ht := (tolerance_spec he).1
  have hu : 0 ≤ 8/epsilon+16 := by positivity
  have hi := tolerance_reciprocal_bound he
  have hT : ((2^stepExponent a epsilon:ℕ):ℝ) ≤ 2*(a:ℝ)^2*(8/epsilon+16) := by
    calc
      _ ≤ 2*(a:ℝ)^2/tolerance epsilon := (stepExponent_spec ha he).2.le
      _ = 2*(a:ℝ)^2*(1/tolerance epsilon) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)
  have hb : (stepExponent a epsilon:ℝ) ≤ 2*(a:ℝ)^2*(8/epsilon+16) :=
    (Nat.cast_le.mpr (show stepExponent a epsilon ≤ 2^stepExponent a epsilon from
      Nat.lt_two_pow_self.le)).trans hT
  have hL : (sampleCount (Fintype.card E) a epsilon:ℝ) ≤
      (Fintype.card E:ℝ)*(a:ℝ)^4*(8/epsilon+16)^4+1 := by
    apply le_trans (sampleCount_spec hq ha he).2.2.le
    have hi4 : (1/tolerance epsilon)^4 ≤ (8/epsilon+16)^4 :=
      pow_le_pow_left₀ (by positivity) hi 4
    have hform : (Fintype.card E:ℝ)*(a:ℝ)^4/(2*tolerance epsilon^4) =
        (Fintype.card E:ℝ)*(a:ℝ)^4*(1/tolerance epsilon)^4/2 := by ring
    rw [hform]
    have hh := mul_le_mul_of_nonneg_left hi4
      (show 0 ≤ (Fintype.card E:ℝ)*(a:ℝ)^4 by positivity)
    have hnn : 0 ≤ (Fintype.card E:ℝ)*(a:ℝ)^4*(8/epsilon+16)^4 := by positivity
    linarith
  rw [binaryOracleIndex_card]
  push_cast
  gcongr
  exact_mod_cast hT

lemma sampledCategorical_sixtytwo {E : Type*} [Fintype E] [DecidableEq E]
    {a : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (62/100:ℝ) * g S ≤
      average (fun bits : BinaryOracleIndex E a (stepExponent a (1/100))
          (sampleCount (Fintype.card E) a (1/100)) → Bool =>
        g (sampledCategorical part hp g (1/100) bits)) := by
  have hgS : 0 ≤ g S := by rw [← hg0]; exact hmono (Finset.empty_subset _)
  have he : 1/Real.exp 1 ≤ (37/100:ℝ) := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  exact (mul_le_mul_of_nonneg_right (by linarith :
    (62/100:ℝ) ≤ 1-1/Real.exp 1-1/100) hgS).trans
      (sampledCategorical_expected part hp g hmono hsub hg0 (by norm_num) S hS)

end MetricKMedianRecovery.Categorical

end OAI
