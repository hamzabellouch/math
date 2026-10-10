import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # The entropy and Poisson exponents in representation multiplicity -/

namespace JointDickman

noncomputable def halfPoissonRate (u : ℝ) : ℝ := 1/2-u+u*Real.log (2*u)
noncomputable def halfRankinExponent (r : ℝ) : ℝ := r*(1+Real.log ((1/2)/r))

/-- This identity is responsible for cancellation of the numeric sieve
and inclusion probability exponents. The conventions at zero agree. -/
theorem halfRankin_sub_halfPoisson (r : ℝ) :
    halfRankinExponent r-halfPoissonRate (1/2-r) = (1/2)*Real.binEntropy (2*r) := by
  have hlog : Real.log ((1/2 : ℝ)/r) = -Real.log (2*r) := by
    rw [show (1/2 : ℝ)/r = (2*r)⁻¹ by simp [mul_inv_rev,div_eq_mul_inv,mul_comm],Real.log_inv]
  unfold halfRankinExponent halfPoissonRate Real.binEntropy
  rw [hlog,show 2*((1/2 : ℝ)-r) = 1-2*r by ring]
  simp only [Real.log_inv]
  ring

/-- A clamped exponential parameter handles the endpoint u=0 without an
infinite tilt. The loss is at most the chosen positive clamp δ. -/
theorem halfPoisson_clamped_chernoff {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let t := -Real.log (2*max δ u)
    0 ≤ t ∧ t ≤ -Real.log (2*δ) ∧
      t*u+(Real.exp (-t)-1)/2 ≤ -halfPoissonRate u+δ := by
  dsimp only
  have hmax : 0 < max δ u := lt_of_lt_of_le hδ (le_max_left _ _)
  have hm1 : max δ u ≤ 1/2 := max_le hδ1 hu1
  have hlog : Real.log (2*max δ u) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hmono : Real.log (2*δ) ≤ Real.log (2*max δ u) :=
    Real.log_le_log (by positivity) (by nlinarith [le_max_left δ u])
  refine ⟨by linarith,by linarith,?_⟩
  rw [neg_neg,Real.exp_log (by positivity)]
  by_cases hdu : δ ≤ u
  · rw [max_eq_right hdu]
    unfold halfPoissonRate
    linarith
  · have huδ : u ≤ δ := le_of_not_ge hdu
    rw [max_eq_left huδ]
    by_cases hu0 : u = 0
    · subst u
      simp only [halfPoissonRate,zero_mul,mul_zero,sub_zero,add_zero]
      linarith
    · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hl : Real.log (2*u) ≤ Real.log (2*δ) := Real.log_le_log (by positivity) (by linarith)
      have hp := mul_le_mul_of_nonneg_left hl hu
      unfold halfPoissonRate
      nlinarith

end JointDickman

end OAI
