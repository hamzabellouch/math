import OAI.NumberTheory.EgyptianFractions.VaughanDyadicUniform
import OAI.NumberTheory.EgyptianFractions.VaughanCutoff

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction

namespace Problem337.Vaughan

/-- The standard three-term envelope for a reduced rational approximation. -/
def approximationEnvelope (X q : ℝ) : ℝ :=
  X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)

lemma approximationEnvelope_nonneg (X q : ℝ) (hX : 0 ≤ X) :
    0 ≤ approximationEnvelope X q := by
  unfold approximationEnvelope
  positivity

lemma dyadic_log_le_three_scale (N : ℕ) :
    1 + Real.log N / Real.log 2 ≤ 3 * typeIILogScale N := by
  have hlog := Real.log_natCast_nonneg N
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hdiv : Real.log N / Real.log 2 ≤ 2 * Real.log N := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right htwo hlog]
  have hN := log_nat_le_typeIILogScale N N le_rfl
  have hH := one_le_typeIILogScale N
  linarith

/-- Balanced cutoffs turn each actual Type II block into the standard envelope. -/
theorem optimized_typeIIBlock_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N j : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j
      (fun k => VaughanBilinear.phase (θ * k))‖ ≤
      18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hq.trans_le hqN
  have hU := optimizedCutoff_pos N hpow
  have hs := typeIIBlock_sq_le_uniform θ a q hq hcop happrox N
    (optimizedCutoff N) (optimizedCutoff N) j hqN hU hU
  have hb := optimizedCutoff_squared_budget N q 32
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j
      (fun k => VaughanBilinear.phase (θ * k))‖
    hN (by exact_mod_cast hq) (by norm_num) hpow hs
  have hsqrt : Real.sqrt (32 : ℝ) ≤ 6 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  change _ ≤ 3 * Real.sqrt 32 * (typeIILogScale N) ^ 3 * approximationEnvelope N q at hb
  refine hb.trans ?_
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  gcongr
  norm_num at *
  linarith

/-- Summing the genuine dyadic blocks costs one further logarithm, not a
power of the summation length. All cancellation hypotheses are discharged. -/
theorem optimized_typeII_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k))
      (typeIICoefficient (optimizedCutoff N) * longPart (optimizedCutoff N) Λ)‖ ≤
      54 * (typeIILogScale N) ^ 4 * approximationEnvelope N q := by
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  have hb := norm_typeII_le_dyadic_log_budget N (optimizedCutoff N) (optimizedCutoff N)
    (fun k => VaughanBilinear.phase (θ * k))
    (18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q) (by positivity)
    (fun j _ => optimized_typeIIBlock_bound θ a q hq hcop happrox N j hqN hpow)
  refine hb.trans ?_
  calc
    _ ≤ (3 * typeIILogScale N) *
        (18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q) :=
      mul_le_mul_of_nonneg_right (dyadic_log_le_three_scale N) (by positivity)
    _ = _ := by ring

end Problem337.Vaughan

end

end OAI
