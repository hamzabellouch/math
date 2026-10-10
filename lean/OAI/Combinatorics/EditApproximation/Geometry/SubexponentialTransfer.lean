import OAI.Combinatorics.EditApproximation.Geometry.ParameterDependencyAsymptotics
import OAI.Combinatorics.EditApproximation.Coarse.CoarseWorkAsymptotics

namespace OAI

/-! Conversion from the computed-height bounds to asymptotics in the actual
input length. The bounds concern scalar envelopes, not an uncharged program. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem fixed_accuracy_large_branch_eventually (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, largeAccuracyInput N epsilon := by
  filter_upwards [eventually_ge_atTop (accuracyCutoff epsilon)] with N hN
  exact accuracyCutoff_sufficient N epsilon hepsilon hN

theorem subexponential_height_to_input (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, Real.exp (f N) ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := hf.eventually (gt_mem_nhds
    (show (0 : ℝ) < epsilon * Real.log 2 / 4 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hfN : f N ≤ (epsilon * Real.log 2 / 4) * inputHeight N :=
    ((div_lt_iff₀ hH).1 hsmall).le
  have hheight := (height_log_sandwich N hN).2
  have hscaled := mul_le_mul_of_nonneg_left hheight
    (show (0 : ℝ) ≤ epsilon * Real.log 2 / 4 by positivity)
  have hcancel : (epsilon * Real.log 2 / 4) *
      ((4 / Real.log 2) * Real.log (N + 2 : ℝ)) = epsilon * Real.log (N + 2 : ℝ) := by
    field_simp [hlogtwo.ne']
  have hexponent : f N ≤ epsilon * Real.log (N + 2 : ℝ) :=
    hfN.trans (hscaled.trans_eq hcancel)
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < N + 2)]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hexponent

theorem sublinear_height_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ (N : ℕ) in atTop, (N + 2 : ℝ) * Real.exp (f N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [subexponential_height_to_input f hf epsilon hepsilon] with N hN
  rw [Real.rpow_add (by positivity : (0 : ℝ) < N + 2), Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hN (by positivity)

noncomputable def computedTotalOverheadExponent (C₁ C₂ C₃ C₄ : ℝ) (N : ℕ) : ℝ :=
  computedDependencyOverheadExponent C₁ C₂ N +
    C₃ * ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N +
    C₄ * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * Real.log (inputHeight N : ℝ)

theorem computedTotalOverheadExponent_tendsto (C₁ C₂ C₃ C₄ : ℝ) :
    Tendsto (fun N => computedTotalOverheadExponent C₁ C₂ C₃ C₄ N / inputHeight N)
      atTop (𝓝 0) := by
  have h := ((computedDependencyOverheadExponent_tendsto C₁ C₂).add
    (local_enumeration_exponent_div_height_tendsto.const_mul C₃)).add
    (encoding_exponent_div_height_tendsto.const_mul C₄)
  simp only [mul_zero, add_zero] at h
  convert h using 1
  ext N
  unfold computedTotalOverheadExponent
  ring

theorem computed_total_overhead_subpolynomial (C₁ C₂ C₃ C₄ epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, Real.exp (computedTotalOverheadExponent C₁ C₂ C₃ C₄ N) ≤
      (N + 2 : ℝ) ^ epsilon :=
  subexponential_height_to_input _
    (computedTotalOverheadExponent_tendsto C₁ C₂ C₃ C₄) epsilon hepsilon

noncomputable def computedCompleteOverheadExponent (C₁ C₂ C₃ C₄ C₅ : ℝ) (N : ℕ) : ℝ :=
  computedTotalOverheadExponent C₁ C₂ C₃ C₄ N + computedCoarseOverheadExponent C₅ N

theorem computedCompleteOverheadExponent_tendsto (C₁ C₂ C₃ C₄ C₅ : ℝ) :
    Tendsto (fun N => computedCompleteOverheadExponent C₁ C₂ C₃ C₄ C₅ N / inputHeight N)
      atTop (𝓝 0) := by
  have h := (computedTotalOverheadExponent_tendsto C₁ C₂ C₃ C₄).add
    (computedCoarseOverheadExponent_tendsto C₅)
  simp only [add_zero] at h
  convert h using 1
  ext N
  unfold computedCompleteOverheadExponent
  ring

/-- The combined coarse, local-enumeration and dependency scalar envelope
is subpolynomial in the actual total input length. -/
theorem computed_complete_overhead_subpolynomial (C₁ C₂ C₃ C₄ C₅ epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, Real.exp (computedCompleteOverheadExponent C₁ C₂ C₃ C₄ C₅ N) ≤
      (N + 2 : ℝ) ^ epsilon :=
  subexponential_height_to_input _
    (computedCompleteOverheadExponent_tendsto C₁ C₂ C₃ C₄ C₅) epsilon hepsilon

end EditApproximation

end OAI
