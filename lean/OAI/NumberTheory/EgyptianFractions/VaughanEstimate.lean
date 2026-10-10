import OAI.NumberTheory.EgyptianFractions.VaughanOptimized
import OAI.NumberTheory.EgyptianFractions.VaughanTypeINormalized

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

lemma realPhase_eq_bilinear_phase (x : ℝ) :
    RealPhase.phase x = VaughanBilinear.phase x :=
  (VaughanBilinear.phase_eq_geometric_phase x).symm

lemma optimized_typeI_scales (X q : ℝ) (hX : 1 ≤ X) (hq : 1 ≤ q)
    (hqX : q ≤ X) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / q + (optimizedCutoff X : ℝ) + q ≤ 4 * approximationEnvelope X q ∧
    X / q + (optimizedCutoff X : ℝ) ^ 2 + q ≤ 4 * approximationEnvelope X q := by
  have hs := optimizedCutoff_standard_envelope X q hX hq hqX hpow
  have hdiv : 0 ≤ X / Real.sqrt (optimizedCutoff X : ℝ) := by positivity
  change _ ≤ 4 * approximationEnvelope X q at hs
  constructor <;> nlinarith [Nat.cast_nonneg (optimizedCutoff X) (α := ℝ),
    sq_nonneg (optimizedCutoff X : ℝ)]

/-- An explicit classical Vaughan estimate for the actual von Mangoldt
exponential sum. The only analytic input is a reduced rational approximation;
all Type I and Type II cancellation estimates have been proved above. -/
theorem vonMangoldt_sum_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
      200 * (typeIILogScale N) ^ 4 * approximationEnvelope N q := by
  let U := optimizedCutoff (N : ℝ)
  let w : ℕ → ℂ := fun k => VaughanBilinear.phase (θ * k)
  let H := typeIILogScale N
  let E := approximationEnvelope (N : ℝ) q
  have hN : 1 ≤ N := hq.trans_le hqN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hH : 1 ≤ H := one_le_typeIILogScale N
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hE : 0 ≤ E := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  have hH14 : H ≤ H ^ 4 := by
    simpa using (pow_le_pow_right₀ hH (show 1 ≤ 4 by omega))
  have hH24 : H ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH (by omega)
  have hcost := optimized_typeI_scales N q hNr hqr hqNr hpow
  have hfirst := VaughanHyperbolic.first_typeI_normalized_bound θ a q hq hcop happrox
    N U hN hqN
  have hsecond := VaughanHyperbolic.second_typeI_normalized_bound θ a q hq hcop happrox
    N U U hN hqN
  simp only [realPhase_eq_bilinear_phase] at hfirst hsecond
  have h1 : ‖weightedSum (Finset.Ioc 0 N) w
      (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤ 64 * H ^ 4 * E := by
    calc
      _ ≤ 16 * H ^ 2 * ((N : ℝ) / q + U + q) := hfirst
      _ ≤ 16 * H ^ 2 * (4 * E) := mul_le_mul_of_nonneg_left hcost.1 (by positivity)
      _ ≤ 64 * H ^ 4 * E := by nlinarith [mul_le_mul_of_nonneg_right hH24 hE]
  have h2 : ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U U * ζ)‖ ≤
      32 * H ^ 4 * E := by
    calc
      _ ≤ 8 * H ^ 2 * ((N : ℝ) / q + (U : ℝ) ^ 2 + q) := by
        simpa only [H, typeIILogScale, w, pow_two] using hsecond
      _ ≤ 8 * H ^ 2 * (4 * E) := mul_le_mul_of_nonneg_left hcost.2 (by positivity)
      _ ≤ 32 * H ^ 4 * E := by nlinarith [mul_le_mul_of_nonneg_right hH24 hE]
  have h0 : ‖weightedSum (Finset.Ioc 0 N) w (shortPart U Λ)‖ ≤ H ^ 4 * E := by
    have hlog : Real.log N ≤ H ^ 4 := (log_nat_le_typeIILogScale N N le_rfl).trans hH14
    have hpower : (N : ℝ) ^ (4 / 5 : ℝ) ≤ E := by
      dsimp [E, approximationEnvelope]
      have hd : 0 ≤ (N : ℝ) / Real.sqrt q := by positivity
      linarith [Real.sqrt_nonneg ((N : ℝ) * q)]
    calc
      _ ≤ (U : ℝ) * Real.log U := norm_short_vonMangoldt_sum_le N U w (by
        intro n hn
        simp [w])
      _ ≤ (N : ℝ) ^ (4 / 5 : ℝ) * Real.log N := optimizedCutoff_log_le N hNr hpow
      _ ≤ E * H ^ 4 := mul_le_mul hpower hlog (Real.log_natCast_nonneg N) hE
      _ = _ := by ring
  have hII : ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart U Λ)‖ ≤
      54 * H ^ 4 * E := optimized_typeII_bound θ a q hq hcop happrox N hqN hpow
  change ‖weightedSum (Finset.Ioc 0 N) w Λ‖ ≤ 200 * H ^ 4 * E
  rw [weighted_identity (Finset.Ioc 0 N) w U U]
  calc
    _ ≤ (‖weightedSum (Finset.Ioc 0 N) w (shortPart U Λ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w
          (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖) +
        ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U U * ζ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart U Λ)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_sub_le _ _).trans
      exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hH0 4) hE]

/-- The ordinary logarithmic form of the classical Vaughan estimate. -/
theorem vonMangoldt_sum_log_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) (hlog : 1 ≤ Real.log N) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
      16200 * (Real.log N) ^ 4 * approximationEnvelope N q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hq.trans_le hqN
  have hH : typeIILogScale N ≤ 3 * Real.log N := by
    unfold typeIILogScale
    rw [Real.log_mul (by norm_num) hNr.ne']
    linarith [Real.log_two_lt_d9]
  have hH0 : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  refine (vonMangoldt_sum_bound θ a q hq hcop happrox N hqN hpow).trans ?_
  calc
    _ ≤ 200 * (3 * Real.log N) ^ 4 * approximationEnvelope N q := by gcongr
    _ = _ := by ring

open Filter in
/-- The estimate holds uniformly in every reduced approximation once the
summation length is large, with an absolute explicit constant. -/
theorem eventually_vonMangoldt_sum_log_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (θ : ℝ) (a : ℤ) (q : ℕ), 0 < q →
      IsCoprime a (q : ℤ) → |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → q ≤ N →
      ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
        16200 * (Real.log N) ^ 4 * approximationEnvelope N q := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hpow : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlog, hpow] with N hlog hpow
  intro θ a q hq hcop happrox hqN
  exact vonMangoldt_sum_log_bound θ a q hq hcop happrox N hqN hpow hlog

end Problem337.Vaughan

end

end OAI
