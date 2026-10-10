import OAI.Combinatorics.EditApproximation.Geometry.ParameterLocalAsymptotics
import OAI.Combinatorics.EditApproximation.Refinement.ComputedStageTime
import OAI.Combinatorics.EditApproximation.Geometry.SeedFactorSchedule

namespace OAI

/-! The actual pass/index count and the exponents in the dependency-path
bound. These statements concern computed numbers, independently of the
proof that an evaluator satisfies the dependency budgets. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem le_fourth_root_of_fourth_power_le {x y : ℝ} (h : x ^ 4 ≤ y) :
    x ≤ Real.sqrt (Real.sqrt y) := by
  apply Real.le_sqrt_of_sq_le
  apply Real.le_sqrt_of_sq_le
  simpa only [← pow_mul] using h

theorem warmup_smallLog_square_div_height_tendsto :
    Tendsto (fun N => ((integerParameters N).T : ℝ) * (inputSmallLog N : ℝ) ^ 2 /
      inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => Real.sqrt (Real.sqrt
      (16 * ((inputSmallLog N : ℝ) ^ 8 / inputHeight N)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      ((smallLog_polynomial_div_height_tendsto 8).const_mul 16).sqrt.sqrt
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hupper
  apply Eventually.of_forall
  intro N
  apply le_fourth_root_of_fourth_power_le
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hT : ((integerParameters N).T : ℝ) ^ 4 ≤ 16 * (inputHeight N : ℝ) ^ 3 := by
    exact_mod_cast (computed_warmup_count_power N).2
  have hmul := mul_le_mul_of_nonneg_right hT
    (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) 8)
  rw [div_pow, mul_pow, ← pow_mul]
  apply (div_le_iff₀ (pow_pos hH 4)).2
  calc
    ((integerParameters N).T : ℝ) ^ 4 * (inputSmallLog N : ℝ) ^ 8 ≤
        16 * (inputHeight N : ℝ) ^ 3 * (inputSmallLog N : ℝ) ^ 8 := hmul
    _ = (16 * ((inputSmallLog N : ℝ) ^ 8 / inputHeight N)) *
        (inputHeight N : ℝ) ^ 4 := by field_simp [hH.ne']

theorem computed_warmup_le_refinement_eventually :
    ∀ᶠ N in atTop, (integerParameters N).T ≤ (integerParameters N).S ∧
      1 ≤ (integerParameters N).S := by
  have hratio := warmup_smallLog_square_div_height_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))] with N hratio hN hell
  have hcount := computed_refinement_count_exact N hN hell
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hproduct : ((integerParameters N).T : ℝ) * (inputSmallLog N : ℝ) ^ 2 < inputHeight N :=
    (div_lt_one hH).1 hratio
  have hT : (integerParameters N).T < (integerParameters N).S := by
    have hproductN : (integerParameters N).T * inputSmallLog N ^ 2 < inputHeight N := by
      exact_mod_cast hproduct
    rw [← hcount] at hproductN
    exact Nat.lt_of_mul_lt_mul_right hproductN
  exact ⟨hT.le, by omega⟩

theorem computed_warmup_div_refinement_tendsto :
    Tendsto (fun N => ((integerParameters N).T : ℝ) / (integerParameters N).S)
      atTop (𝓝 0) := by
  apply warmup_smallLog_square_div_height_tendsto.congr'
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))] with N hN hell
  rw [computed_refinement_count_real N hN hell]
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hellpos : (0 : ℝ) < inputSmallLog N := by exact_mod_cast Nat.two_pow_pos (smallLogExponent N)
  field_simp [hH.ne', hellpos.ne']

theorem scalar_pass_count_bound (p e ell f K : ℝ)
    (hp : 0 ≤ p) (hf : 4 ≤ f) (helf : f ≤ ell) (heel : e ≤ ell)
    (hK : K ≤ (p + 4) * e / (f - 2) + 2) :
    K ≤ 10 * (p + 1) * ell / f := by
  have hfpos : 0 < f := by linarith
  have hden : 0 < f - 2 := by linarith
  have hqell : 0 ≤ (p + 1) * ell := mul_nonneg (by linarith) (by linarith)
  have hnum : (p + 4) * e ≤ 4 * (p + 1) * ell := by
    have h := mul_le_mul_of_nonneg_left heel (by linarith : 0 ≤ p + 4)
    nlinarith [mul_nonneg hp (show 0 ≤ ell by linarith)]
  have hmain : (p + 4) * e / (f - 2) ≤ 8 * (p + 1) * ell / f := by
    apply (div_le_div_iff₀ hden hfpos).2
    have hnumf := mul_le_mul_of_nonneg_right hnum hfpos.le
    have hslack := mul_nonneg hqell (show 0 ≤ f - 4 by linarith)
    nlinarith
  have hconst : 2 ≤ 2 * (p + 1) * ell / f := by
    apply (le_div_iff₀ hfpos).2
    nlinarith [mul_nonneg hp (show 0 ≤ ell by linarith)]
  calc
    K ≤ (p + 4) * e / (f - 2) + 2 := hK
    _ ≤ 8 * (p + 1) * ell / f + 2 * (p + 1) * ell / f := add_le_add hmain hconst
    _ = 10 * (p + 1) * ell / f := by ring

theorem computed_pass_count_bound (N : ℕ) (hN : 0 < N) (hf : 4 ≤ smallLogExponent N) :
    (computedSeedPassCount N + 1 : ℝ) ≤
      10 * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N / smallLogExponent N := by
  apply scalar_pass_count_bound (e := (heightExponent N : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast hf
  · have h := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)) (n := smallLogExponent N)).le
    exact_mod_cast h
  · exact_mod_cast (inputSmallLog_bounds N hN).1
  · have hraw := dyadicSeedPassCount_le (smallLogExponent N) (computedSeedInitialExponent N) (by omega)
    have hcast : (computedSeedPassCount N : ℝ) ≤
        ((computedSeedInitialExponent N / (smallLogExponent N - 2) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hraw
    have hdiv : ((computedSeedInitialExponent N / (smallLogExponent N - 2) : ℕ) : ℝ) ≤
        (computedSeedInitialExponent N : ℝ) / (smallLogExponent N - 2 : ℕ) := Nat.cast_div_le
    have hden : ((smallLogExponent N - 2 : ℕ) : ℝ) = (smallLogExponent N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ smallLogExponent N)]
      norm_num
    rw [hden] at hdiv
    have hexp : (computedSeedInitialExponent N : ℝ) =
        ((coarseExponent (inputSmallLog N) : ℝ) + 4) * heightExponent N := by
      simp only [computedSeedInitialExponent, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    rw [hexp] at hdiv
    linarith

def computedDependencyIndexCount (N : ℕ) : ℕ :=
  (computedSeedPassCount N + 1) * ((integerParameters N).T + (integerParameters N).S + 1)

theorem scalar_dependency_index_bound (p ell f H S T K : ℝ)
    (hell : 0 < ell) (hf : 0 < f) (hS : 1 ≤ S) (hT : T ≤ S)
    (hK : 0 ≤ K) (hcount : S * ell ^ 2 = H)
    (hpass : K ≤ 10 * (p + 1) * ell / f) :
    K * (T + S + 1) ≤ 30 * H * (p + 1) / (ell * f) := by
  calc
    K * (T + S + 1) ≤ K * (3 * S) := mul_le_mul_of_nonneg_left (by linarith) hK
    _ ≤ (10 * (p + 1) * ell / f) * (3 * S) :=
      mul_le_mul_of_nonneg_right hpass (by linarith)
    _ = 30 * H * (p + 1) / (ell * f) := by
      rw [← hcount]
      field_simp [hell.ne', hf.ne']
      ring

theorem computed_dependency_index_bound_eventually :
    ∀ᶠ N in atTop, (computedDependencyIndexCount N : ℝ) ≤
      30 * (inputHeight N : ℝ) * ((coarseExponent (inputSmallLog N) : ℝ) + 1) /
        ((inputSmallLog N : ℝ) * smallLogExponent N) := by
  filter_upwards [computed_warmup_le_refinement_eventually, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    smallLogExponent_tendsto.eventually (eventually_ge_atTop 4)] with N htime hN hell hf
  have h := scalar_dependency_index_bound
    (coarseExponent (inputSmallLog N)) (inputSmallLog N) (smallLogExponent N)
    (inputHeight N) ((integerParameters N).S) ((integerParameters N).T)
    (computedSeedPassCount N + 1)
    (by exact_mod_cast Nat.two_pow_pos (smallLogExponent N))
    (by exact_mod_cast (show 0 < smallLogExponent N by omega))
    (by exact_mod_cast htime.2) (by exact_mod_cast htime.1) (by positivity)
    (by exact_mod_cast computed_refinement_count_exact N hN hell)
    (computed_pass_count_bound N hN hf)
  simpa only [computedDependencyIndexCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h

theorem coarse_shifted_square_div_smallExponent_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) ^ 2 /
      smallLogExponent N) atTop (𝓝 0) := by
  have h := coarse_shifted_square_div_log_tendsto.const_mul (Real.log 2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hf
  rw [inputSmallLog_real_log]
  have hfn : (smallLogExponent N : ℝ) ≠ 0 := by exact_mod_cast (show smallLogExponent N ≠ 0 by omega)
  have hc : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hfn, hc]

theorem scalar_weighted_dependency_bound (q k e ell f H c : ℝ)
    (hq : 0 ≤ q) (hk : 0 ≤ k) (heel : e ≤ ell)
    (hell : 0 < ell) (hf : 0 < f) (hH : 0 < H) (hc : 0 ≤ c)
    (hbound : k ≤ 30 * H * q / (ell * f)) :
    q * k * (e * c) / H ≤ 30 * c * q ^ 2 / f := by
  have hproduct : k * (ell * f) ≤ 30 * H * q :=
    (le_div_iff₀ (mul_pos hell hf)).1 hbound
  apply (div_le_div_iff₀ hH hf).2
  calc
    q * k * (e * c) * f = k * (e * f) * (q * c) := by ring
    _ ≤ k * (ell * f) * (q * c) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hq hc)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right heel hf.le) hk
    _ ≤ (30 * H * q) * (q * c) := mul_le_mul_of_nonneg_right hproduct (mul_nonneg hq hc)
    _ = 30 * c * q ^ 2 * H := by ring

/-- The exponent of the earlier-index branching factor is `o(H)`. -/
theorem weighted_dependency_div_height_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
      computedDependencyIndexCount N * Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) := by
  have hupper := coarse_shifted_square_div_smallExponent_tendsto.const_mul (30 * Real.log 2)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [computed_dependency_index_bound_eventually, eventually_ge_atTop 1,
    smallLogExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hbound hN hf
  have hlog : Real.log (inputHeight N : ℝ) = (heightExponent N : ℝ) * Real.log 2 := by
    simp only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog]
  simpa only [mul_div_assoc] using scalar_weighted_dependency_bound
    ((coarseExponent (inputSmallLog N) : ℝ) + 1) (computedDependencyIndexCount N)
    (heightExponent N) (inputSmallLog N) (smallLogExponent N) (inputHeight N) (Real.log 2)
    (by positivity) (Nat.cast_nonneg _)
    (by exact_mod_cast (inputSmallLog_bounds N hN).1)
    (by exact_mod_cast Nat.two_pow_pos (smallLogExponent N))
    (by exact_mod_cast (show 0 < smallLogExponent N by omega))
    (by exact_mod_cast Nat.two_pow_pos (heightExponent N))
    (Real.log_nonneg (by norm_num)) hbound

def computedMaxTreeDepth (N : ℕ) : ℕ := intervalTreeDepth (integerParameters N).M N

theorem intervalTreeDepth_le_computedMax (N nx : ℕ) (hnx : nx ≤ N) :
    intervalTreeDepth (integerParameters N).M nx ≤ computedMaxTreeDepth N :=
  Nat.clog_mono_right _ (max_le_max le_rfl hnx)

/-- A uniform depth upper bound is obtained by using the total length as
the source length. -/
theorem tree_logSmallLog_div_height_tendsto :
    Tendsto (fun N => (computedMaxTreeDepth N : ℝ) *
      Real.log (inputSmallLog N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper := log_smallLog_div_smallLog_tendsto.const_mul 100
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  have hbound : (computedMaxTreeDepth N : ℝ) * inputSmallLog N ≤ 100 * (inputHeight N : ℝ) := by
    exact_mod_cast computed_tree_depth_bound N N hN le_rfl hell
  have hlog : 0 ≤ Real.log (inputSmallLog N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hellpos : (0 : ℝ) < inputSmallLog N := by exact_mod_cast Nat.two_pow_pos (smallLogExponent N)
  have hscaled := mul_le_mul_of_nonneg_right hbound hlog
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hH hellpos).2
  nlinarith only [hscaled]

theorem tree_depth_div_height_tendsto :
    Tendsto (fun N => (computedMaxTreeDepth N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ tree_logSmallLog_div_height_tendsto
  filter_upwards [(Real.tendsto_log_atTop.comp inputSmallLog_real_tendsto).eventually
    (eventually_ge_atTop 1)] with N hlog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hlog

theorem dependency_index_div_height_tendsto :
    Tendsto (fun N => (computedDependencyIndexCount N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ weighted_dependency_div_height_tendsto
  filter_upwards [(Real.tendsto_log_atTop.comp inputHeight_real_tendsto).eventually
    (eventually_ge_atTop 1)] with N hlog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (computedDependencyIndexCount N : ℝ) ≤
        ((coarseExponent (inputSmallLog N) : ℝ) + 1) * computedDependencyIndexCount N := by
      have hm : (0 : ℝ) ≤ (coarseExponent (inputSmallLog N) : ℝ) * computedDependencyIndexCount N :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [hm]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hlog

noncomputable def computedDependencyOverheadExponent (C₁ C₂ : ℝ) (N : ℕ) : ℝ :=
  (1 + Real.log 2) * ((computedMaxTreeDepth N : ℝ) + computedDependencyIndexCount N + 2) +
    C₁ * computedMaxTreeDepth N * Real.log (inputSmallLog N : ℝ) +
    C₂ * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * computedDependencyIndexCount N *
      Real.log (inputHeight N : ℝ)

/-- Every fixed choice of the two branching-budget constants yields a
sublinear logarithmic overhead in the dependency-path bound. -/
theorem computedDependencyOverheadExponent_tendsto (C₁ C₂ : ℝ) :
    Tendsto (fun N => computedDependencyOverheadExponent C₁ C₂ N / inputHeight N)
      atTop (𝓝 0) := by
  have htwo : Tendsto (fun N => 2 / (inputHeight N : ℝ)) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero, div_eq_mul_inv] using inputHeight_real_tendsto.inv_tendsto_atTop.const_mul 2
  have h := (((tree_depth_div_height_tendsto.add dependency_index_div_height_tendsto).add htwo).const_mul
    (1 + Real.log 2)).add ((tree_logSmallLog_div_height_tendsto.const_mul C₁).add
      (weighted_dependency_div_height_tendsto.const_mul C₂))
  simp only [zero_add, mul_zero] at h
  convert h using 1
  ext N
  unfold computedDependencyOverheadExponent
  ring

end EditApproximation

end OAI
