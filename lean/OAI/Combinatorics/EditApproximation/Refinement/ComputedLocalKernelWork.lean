import OAI.Combinatorics.EditApproximation.Refinement.ComputedWidthEnvelope
import OAI.Combinatorics.EditApproximation.Refinement.ComputedPhysicalWork

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 def localKernelPowerExponent (M p D : ℕ) : ℕ := ((100 * M + 100000) * (p + 1)) * D

 def computedLocalKernelBudget (D N : ℕ) : ℕ :=
  inputHeight N ^ localKernelPowerExponent (integerParameters N).M
    (coarseExponent (inputSmallLog N)) D

noncomputable def computedLocalKernelExponent (D N : ℕ) : ℝ :=
  (D : ℝ) * ((100 * Real.log 2) * ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N +
    100000 * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * Real.log (inputHeight N : ℝ))

 theorem computedLocalKernelExponent_tendsto (D : ℕ) :
    Tendsto (fun N => computedLocalKernelExponent D N / inputHeight N) atTop (𝓝 0) := by
  have h := ((local_enumeration_exponent_div_height_tendsto.const_mul (100 * Real.log 2)).add
    (encoding_exponent_div_height_tendsto.const_mul 100000)).const_mul (D : ℝ)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  ext N
  unfold computedLocalKernelExponent
  ring

private theorem localKernelBudget_exp_scalar (D H M p ell : ℕ) (hH : 0 < H)
    (hlog : Real.log (H : ℝ) ≤ (ell : ℝ) * Real.log 2) :
    ((H ^ localKernelPowerExponent M p D : ℕ) : ℝ) ≤
      Real.exp ((D : ℝ) * ((100 * Real.log 2) * (M : ℝ) * ((p : ℝ) + 1) * ell +
        100000 * ((p : ℝ) + 1) * Real.log (H : ℝ))) := by
  rw [Nat.cast_pow, nat_pow_eq_exp_log H _ hH]
  apply Real.exp_le_exp.mpr
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (p : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hM) hp)
  have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  unfold localKernelPowerExponent
  push_cast
  nlinarith only [mul_nonneg hD (sub_nonneg.mpr hmul)]

 theorem computedLocalKernelBudget_exp_bound (D N : ℕ) (hN : 0 < N) :
    (computedLocalKernelBudget D N : ℝ) ≤ Real.exp (computedLocalKernelExponent D N) := by
  have hlog : Real.log (inputHeight N : ℝ) ≤ (inputSmallLog N : ℝ) * Real.log 2 := by
    rw [inputHeight_real_log]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (inputSmallLog_bounds N hN).1)
      (Real.log_nonneg (by norm_num))
  exact localKernelBudget_exp_scalar D (inputHeight N) (integerParameters N).M
    (coarseExponent (inputSmallLog N)) (inputSmallLog N) (Nat.two_pow_pos _) hlog

 theorem computedLocalKernelBudget_subpolynomial (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, (computedLocalKernelBudget D N : ℝ) ≤ (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input (computedLocalKernelExponent D)
    (computedLocalKernelExponent_tendsto D) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  exact (computedLocalKernelBudget_exp_bound D N (by omega)).trans he

 theorem computedLocalKernelBudget_envelope_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * computedLocalKernelBudget D N ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear (computedLocalKernelExponent D)
    (computedLocalKernelExponent_tendsto D) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  exact (mul_le_mul_of_nonneg_left (computedLocalKernelBudget_exp_bound D N (by omega))
    (computedWidthEnvelope_nonneg N)).trans he

 theorem computedLocalKernelBudget_widthWork_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) * computedLocalKernelBudget D N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computed_widthWork_subexponential (computedLocalKernelExponent D)
    (computedLocalKernelExponent_tendsto D) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  intro n hn tree hv hd hk
  exact (mul_le_mul_of_nonneg_left (computedLocalKernelBudget_exp_bound D N (by omega))
    (Nat.cast_nonneg _)).trans (he n hn tree hv hd hk)

 theorem computedLocalKernelBudget_requests_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) * computedLocalKernelBudget D N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedFamilyResult_requests_near_linear (epsilon / 2) hh,
    computedLocalKernelBudget_subpolynomial D (epsilon / 2) hh] with N hr hk
  intro source target hsize input
  calc
    _ ≤ (N + 2 : ℝ) ^ (1 + epsilon / 2) * (N + 2 : ℝ) ^ (epsilon / 2) :=
      mul_le_mul (hr source target hsize input) hk (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
