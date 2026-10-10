import OAI.Combinatorics.EditApproximation.Refinement.ComputedActualBandWork

namespace OAI

/-! A parameter-only majorant for every executed dependency tree. It is
independent of the accepted random values and of all accuracy events. -/

namespace EditApproximation

open Filter
open scoped Topology

noncomputable def computedWidthEnvelope (N : ℕ) : ℝ :=
  (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 *
    Real.exp (computedDependencyOverheadExponent 257 512 N)

theorem computedWidthEnvelope_nonneg (N : ℕ) : 0 ≤ computedWidthEnvelope N := by
  unfold computedWidthEnvelope
  positivity

theorem computed_widthWork_le_envelope (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) (hH : 105 ≤ inputHeight N)
    (tree : DependencyExpansion)
    (hv : tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))))
    (hd : tree.depth = intervalTreeDepth (integerParameters N).M n)
    (hk : tree.rank ≤ computedDependencyIndexCount N) :
    (tree.widthWork (integerParameters N).M n : ℝ) ≤ computedWidthEnvelope N := by
  have hw := DependencyExpansion.widthWork_le (integerParameters N).M n _ _ _
    (computed_branching_bounds N hN hell).1 tree hv hd hk
    (Real.exp (computedDependencyOverheadExponent 257 512 N)) (Real.exp_nonneg _) (by
      intro j hj
      exact computed_dependency_path_envelope N 257 512 j
        (hj.trans (intervalTreeDepth_le_computedMax N n hn)))
  have hpref := computed_width_prefactor_le N n hN hn hell hH
  have hprefR : (((intervalTreeDepth (integerParameters N).M n + 1) * n +
      4 * (integerParameters N).M * max 1 n : ℕ) : ℝ) ≤
      (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hpref
  exact hw.trans (mul_le_mul_of_nonneg_right hprefR (Real.exp_nonneg _))

theorem computedWidthEnvelope_mul_exp_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * Real.exp (f N) ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := ((computedDependencyOverheadExponent_tendsto 257 512).add
    (hlog.const_mul 2)).add hf
  simp only [mul_zero, add_zero] at hlimit
  have hfinal := sublinear_height_near_linear
    (fun N => computedDependencyOverheadExponent 257 512 N +
      2 * Real.log (inputHeight N : ℝ) + f N) (by
        convert hlimit using 1
        ext N
        ring) epsilon hepsilon
  filter_upwards [hfinal] with N hN
  convert hN using 1
  unfold computedWidthEnvelope
  rw [Real.exp_add, Real.exp_add]
  have hp : Real.exp (2 * Real.log (inputHeight N : ℝ)) = (inputHeight N : ℝ) ^ 2 := by
    simpa using (nat_pow_eq_exp_log (inputHeight N) 2 (Nat.two_pow_pos _)).symm
  rw [hp]
  ring

theorem computedWidthEnvelope_weighted_near_linear (C : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * (inputHeight N : ℝ) ^ C ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (C : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((C : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1; ext N; ring
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) C (Nat.two_pow_pos _)] at hN

theorem computedWidthEnvelope_coarse_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * computedCoarseWidthOverhead N ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear _
    (computedCoarseOverheadExponent_tendsto 10) epsilon hepsilon, eventually_ge_atTop 1] with N hN hpos
  exact (mul_le_mul_of_nonneg_left (computedCoarseWidthOverhead_exp_le N (by omega))
    (computedWidthEnvelope_nonneg N)).trans hN

theorem computedWidthEnvelope_band_near_linear (C : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * computedActualBandBitBudget C N ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear _
    (computedActualBandBitExponent_tendsto C) epsilon hepsilon, eventually_ge_atTop 1] with N hN hpos
  exact (mul_le_mul_of_nonneg_left (computedActualBandBitBudget_exp_bound C N (by omega))
    (computedWidthEnvelope_nonneg N)).trans hN

end EditApproximation

end OAI
