import OAI.Combinatorics.EditApproximation.Geometry.ParameterLocalAsymptotics
import OAI.Combinatorics.EditApproximation.Coarse.CoarseParameters
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialWork

namespace OAI

/-! The depth-dependent scalar overhead of the actual initial estimator.
The expected array-counter bound includes every pruning outcome. -/

namespace EditApproximation

open Filter
open scoped Topology

def computedMaxCoarseDepth (N : ℕ) : ℕ := computedCoarseDepth N N

theorem computedCoarseDepth_le_max (N n : ℕ) (hn : n ≤ N) :
    computedCoarseDepth N n ≤ computedMaxCoarseDepth N := by
  change Nat.clog (integerParameters N).B (max 1 n) ≤ Nat.clog (integerParameters N).B (max 1 N)
  exact Nat.clog_mono_right (integerParameters N).B (max_le_max le_rfl hn)

theorem coarse_depth_mul_exponent_bound (N : ℕ) :
    computedMaxCoarseDepth N * (heightExponent N * coarseExponent (inputSmallLog N)) ≤
      inputHeight N + heightExponent N * coarseExponent (inputSmallLog N) := by
  let e := heightExponent N * coarseExponent (inputSmallLog N)
  have hB : (integerParameters N).B = 2 ^ e := by
    simp only [integerParameters, inputHeight, ← pow_mul, e]
  have hdepth : computedMaxCoarseDepth N = (Nat.clog 2 (max 1 N) + (e - 1)) / e := by
    unfold computedMaxCoarseDepth computedCoarseDepth
    rw [hB, Nat.clog_pow_left]
  have hlength : max 1 N ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact (Nat.le_add_right N 2).trans (inputHeight_covers_length N)
  have hlog : Nat.clog 2 (max 1 N) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength
  have hprod := Nat.div_mul_le_self (Nat.clog 2 (max 1 N) + (e - 1)) e
  rw [← hdepth] at hprod
  exact hprod.trans (Nat.add_le_add hlog (Nat.sub_le _ _))

theorem scalar_coarse_depth_log_bound (D e p H c : ℝ)
    (hp : 0 < p) (hH : 0 < H) (hc : 0 ≤ c)
    (hbound : D * (e * p) ≤ H + e * p) :
    D * (e * c) / H ≤ e * c / H + c / p := by
  have hDe : D * e ≤ H / p + e := by
    calc
      D * e ≤ (H + e * p) / p := (le_div_iff₀ hp).2 (by nlinarith only [hbound])
      _ = H / p + e := by field_simp [hp.ne']
  have hmul := mul_le_mul_of_nonneg_right hDe hc
  have hdiv := div_le_div_of_nonneg_right hmul hH.le
  calc
    D * (e * c) / H = (D * e) * c / H := by ring
    _ ≤ (H / p + e) * c / H := hdiv
    _ = e * c / H + c / p := by field_simp [hp.ne', hH.ne']; ring

theorem coarse_depth_log_height_div_height_tendsto :
    Tendsto (fun N => (computedMaxCoarseDepth N : ℝ) *
      Real.log (inputHeight N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hinv : Tendsto (fun N => Real.log 2 / (coarseExponent (inputSmallLog N) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero, div_eq_mul_inv] using
      coarseExponent_real_tendsto.inv_tendsto_atTop.const_mul (Real.log 2)
  have hupper := hlog.add hinv
  simp only [zero_add] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [coarseExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hp
  have hbound : (computedMaxCoarseDepth N : ℝ) *
      ((heightExponent N : ℝ) * coarseExponent (inputSmallLog N)) ≤
      (inputHeight N : ℝ) + (heightExponent N : ℝ) * coarseExponent (inputSmallLog N) := by
    exact_mod_cast coarse_depth_mul_exponent_bound N
  rw [inputHeight_real_log]
  exact scalar_coarse_depth_log_bound _ _ _ _ _
    (by exact_mod_cast (show 0 < coarseExponent (inputSmallLog N) by omega))
    (by exact_mod_cast Nat.two_pow_pos (heightExponent N))
    (Real.log_nonneg (by norm_num)) hbound

noncomputable def computedCoarseOverheadExponent (C : ℝ) (N : ℕ) : ℝ :=
  C * ((computedMaxCoarseDepth N : ℝ) + coarseExponent (inputSmallLog N) + 1) *
    Real.log (inputHeight N : ℝ)

theorem computedCoarseOverheadExponent_tendsto (C : ℝ) :
    Tendsto (fun N => computedCoarseOverheadExponent C N / inputHeight N) atTop (𝓝 0) := by
  have h := (coarse_depth_log_height_div_height_tendsto.add
    encoding_exponent_div_height_tendsto).const_mul C
  simp only [zero_add, mul_zero] at h
  convert h using 1
  ext N
  unfold computedCoarseOverheadExponent
  ring

theorem coarse_branching_log_div_height_tendsto :
    Tendsto (fun N => Real.log ((integerParameters N).B : ℝ) / inputHeight N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have h := encoding_exponent_div_height_tendsto.sub hlog
  simp only [sub_zero] at h
  convert h using 1
  ext N
  simp only [integerParameters, Nat.cast_pow, Real.log_pow]
  ring

/-- The literal coarse threshold law has the paper's `H^8` inverse-allowance
factor, for all sufficiently large inputs and without any accuracy event. -/
theorem coarse_inverse_allowance_le_height_eight_eventually :
    ∀ᶠ N in atTop, coarseInverseAllowanceFactor (integerParameters N).B
      (initialThresholdQ N) (initialLambda N) ≤ (inputHeight N : ℝ) ^ 8 := by
  have hratio := coarse_branching_log_div_height_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, inputHeight_real_tendsto.eventually (eventually_ge_atTop 128)] with N hratio hlarge
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hlog : Real.log ((integerParameters N).B : ℝ) ≤ inputHeight N :=
    ((div_lt_one hH).1 hratio).le
  have hraw := coarseInverseAllowanceFactor_log_bound (integerParameters N).B
    (initialThresholdQ N) (initialLambda N)
    (by unfold initialThresholdQ; positivity) (by unfold initialLambda; positivity)
  have hfactor : ((initialThresholdQ N : ℚ) : ℝ) / ((initialLambda N : ℚ) : ℝ) =
      64 * (inputHeight N : ℝ) ^ 5 := by
    simp only [initialThresholdQ, initialLambda, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    field_simp [hH.ne']
  rw [hfactor] at hraw
  have hstep : 1 + Real.log ((integerParameters N).B : ℝ) ≤ 2 * (inputHeight N : ℝ) := by
    linarith
  calc
    _ ≤ 64 * (inputHeight N : ℝ) ^ 5 * (1 + Real.log ((integerParameters N).B : ℝ)) := hraw
    _ ≤ 64 * (inputHeight N : ℝ) ^ 5 * (2 * (inputHeight N : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 128 * (inputHeight N : ℝ) ^ 6 := by ring
    _ ≤ (inputHeight N : ℝ) ^ 2 * (inputHeight N : ℝ) ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = (inputHeight N : ℝ) ^ 8 := by ring

end EditApproximation

end OAI
