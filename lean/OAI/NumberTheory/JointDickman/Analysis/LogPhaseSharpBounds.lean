import OAI.NumberTheory.JointDickman.Analysis.LogPhaseFirstDerivative
import OAI.NumberTheory.JointDickman.Analysis.LogPhaseSecondDerivative

namespace OAI

/-! # Sharp dyadic logarithmic sums in the first two derivative ranges -/
namespace JointDickman
open Finset Problem337
open scoped ComplexConjugate

lemma log_phase_sum_neg (Z : ℝ) (L R : ℕ) :
    (∑ n ∈ Icc L R, ExponentialSum.phase (-Z*Real.log (n:ℝ))) =
      conj (∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))) := by
  simp only [map_sum, neg_mul, ExponentialSum.phase_neg]

lemma log_phase_sum_trivial {U : ℝ} (hU : 1 ≤ U) (Z : ℝ) (L R : ℕ)
    (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 3*U := by
  calc
    _ ≤ ∑ n ∈ Icc L R, ‖ExponentialSum.phase (Z*Real.log (n:ℝ))‖ := norm_sum_le _ _
    _ = ((Icc L R).card:ℝ) := by simp only [ExponentialSum.phase_norm, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (R:ℝ)+1 := by
      exact_mod_cast (show (Icc L R).card ≤ R+1 by rw [Nat.card_Icc]; omega)
    _ ≤ 3*U := by linarith

lemma log_phase_second_bound {U Z : ℝ} (hU : 1 ≤ U)
    (hZ : U/4 ≤ |Z|) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
      2000*Real.sqrt |Z| := by
  have hU0 : 0 < U := by linarith
  have hZ0 : 0 < |Z| := by linarith
  by_cases hLR : L ≤ R
  · let N := R+1-L
    have hN : (L:ℝ)+(N:ℝ) = (R:ℝ)+1 := by
      exact_mod_cast (show L+N=R+1 by dsimp [N]; omega)
    have hNle : (N:ℝ) ≤ 2*U := by linarith
    have hh := logarithmic_difference_sum_bound [] (by simp) 0 Z U L N
      (abs_pos.mp hZ0) hU0 hL (by simp only [List.sum_nil, add_zero]; linarith)
    simp only [List.prod_nil, List.length_nil, zero_add, Nat.factorial_one,
      Nat.cast_one, one_mul, forwardDifference, zero_mul] at hh
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hh
    have hs : Real.sqrt (|Z|/(4*U)^2) = Real.sqrt |Z|/(4*U) := by
      rw [Real.sqrt_div (abs_nonneg _), Real.sqrt_sq (by positivity)]
    rw [hs] at hh
    have hsq : (Real.sqrt |Z|)^2 = |Z| := Real.sq_sqrt hZ0.le
    have hsqrt : 0 < Real.sqrt |Z| := Real.sqrt_pos.mpr hZ0
    have hn : (N:ℝ)*(Real.sqrt |Z|/(4*U)) ≤ Real.sqrt |Z| := by
      calc
        _ = ((N:ℝ)/(4*U))*Real.sqrt |Z| := by ring
        _ ≤ 1*Real.sqrt |Z| := mul_le_mul_of_nonneg_right
          ((div_le_one (by positivity)).mpr (by linarith)) (Real.sqrt_nonneg |Z|)
        _ = _ := one_mul _
    have hi : 1/(Real.sqrt |Z|/(4*U)) ≤ 16*Real.sqrt |Z| := by
      rw [one_div_div]
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith
    have hset : Icc L R = Ico L (R+1) := by ext n; simp
    rw [hset, sum_Ico_eq_sum_range]
    have he : (∑ k ∈ range (R+1-L), ExponentialSum.phase (Z*Real.log ((L+k:ℕ):ℝ))) =
        ∑ j ∈ range N, ExponentialSum.phase (Z*Real.log ((j:ℝ)+(L:ℝ))) := by
      apply sum_congr rfl
      intro j _
      simp only [Nat.cast_add, add_comm]
    rw [he]
    apply hh.trans
    nlinarith
  · rw [Icc_eq_empty (by omega), sum_empty, norm_zero]
    positivity

/-- Uniform sharp-interval estimate. The square-root term is used only
above the first derivative range. -/
theorem log_phase_sharp_bound {U : ℝ} (hU : 1 ≤ U) (Z : ℝ) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
      2000*(U/(1+|Z|)+Real.sqrt |Z|) := by
  have hU0 : 0 < U := by linarith
  by_cases hz : |Z| ≤ 1
  · have hu : 3*U ≤ 2000*(U/(1+|Z|)+Real.sqrt |Z|) := by
      have hd : U/2 ≤ U/(1+|Z|) :=
        div_le_div_of_nonneg_left hU0.le (by positivity) (by linarith)
      nlinarith [Real.sqrt_nonneg |Z|]
    exact (log_phase_sum_trivial hU Z L R hR).trans hu
  · by_cases hhi : U/4 ≤ |Z|
    · apply (log_phase_second_bound hU hhi L R hL hR).trans
      have hd : 0 ≤ U/(1+|Z|) := by positivity
      nlinarith
    · have hpos : 0 < |Z| := lt_trans zero_lt_one (lt_of_not_ge hz)
      have hh : ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 8*U/|Z| := by
        by_cases hp : 0 ≤ Z
        · simpa only [abs_of_nonneg hp] using
            positive_log_phase_first_bound hU (by simpa only [abs_of_nonneg hp] using hpos)
              (by simpa only [abs_of_nonneg hp] using le_of_not_ge hhi) L R hL hR
        · have hn : |Z| = -Z := abs_of_neg (lt_of_not_ge hp)
          have hh := positive_log_phase_first_bound hU hpos (le_of_not_ge hhi) L R hL hR
          rw [hn, log_phase_sum_neg, Complex.norm_conj] at hh
          simpa only [hn] using hh
      apply hh.trans
      have hd : U/|Z| ≤ 2*(U/(1+|Z|)) := by
        rw [show 2*(U/(1+|Z|)) = (2*U)/(1+|Z|) by ring]
        apply (div_le_div_iff₀ hpos (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left (show 1+|Z| ≤ 2*|Z| by linarith) hU0.le]
      have hd0 : 0 ≤ U/(1+|Z|) := by positivity
      calc
        _ = 8*(U/|Z|) := by ring
        _ ≤ 8*(2*(U/(1+|Z|))) := mul_le_mul_of_nonneg_left hd (by norm_num)
        _ ≤ _ := by nlinarith [Real.sqrt_nonneg |Z|]

end JointDickman

end OAI
