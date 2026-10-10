import OAI.Analysis.FiniteFactor.Sampling.Fourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Ring.GeomSum

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ComplexConjugate
noncomputable section

def samplingCharacter (v : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * v * t)

theorem samplingCharacter_norm (v : ℤ) (t : ℝ) : ‖samplingCharacter v t‖ = 1 := by
  simp [samplingCharacter, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem samplingCharacter_continuous (v : ℤ) : Continuous (samplingCharacter v) := by
  unfold samplingCharacter
  fun_prop

theorem samplingCharacter_zero (t : ℝ) : samplingCharacter 0 t = 1 := by simp [samplingCharacter]

theorem samplingCharacter_add (v w : ℤ) (t : ℝ) :
    samplingCharacter (v+w) t = samplingCharacter v t * samplingCharacter w t := by
  unfold samplingCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem samplingCharacter_neg (v : ℤ) (t : ℝ) :
    samplingCharacter (-v) t = conj (samplingCharacter v t) := by
  have htwo : conj (2 : ℂ) = 2 := by
    change conj ((2 : ℝ) : ℂ) = _
    exact Complex.conj_ofReal _
  simp [samplingCharacter, ← Complex.exp_conj, mul_assoc, htwo]

theorem samplingCharacter_sub (v w : ℤ) (t : ℝ) :
    samplingCharacter (v-w) t = samplingCharacter v t * conj (samplingCharacter w t) := by
  rw [sub_eq_add_neg, samplingCharacter_add, samplingCharacter_neg]

theorem samplingCharacter_integrable (v : ℤ) :
    Integrable (samplingCharacter v) unitIntervalMeasure :=
  (samplingCharacter_continuous v).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

theorem samplingCharacter_integral (v : ℤ) :
    (∫ t, samplingCharacter v t ∂unitIntervalMeasure) = if v = 0 then 1 else 0 := by
  by_cases hv : v = 0
  · subst v; simp [samplingCharacter_zero]
  rw [ite_eq_right hv]
  unfold unitIntervalMeasure
  rw [restrict_Ico_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ t in (0 : ℝ)..1, Complex.exp ((2 * Real.pi * Complex.I * (v : ℂ)) * t)) = 0
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have hcoef : 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) hvC
  rw [integral_exp_mul_complex hcoef]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) = (v : ℂ)*(2*Real.pi*Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The finite Fejer kernel, as a nonnegative real function. -/
def samplingKernel (H : ℕ) (t : ℝ) : ℝ :=
  ‖∑ r ∈ Finset.range H, samplingCharacter (r : ℤ) t‖^2 / (H : ℝ)

theorem samplingKernel_nonneg (H : ℕ) (t : ℝ) : 0 ≤ samplingKernel H t := by
  unfold samplingKernel
  positivity

theorem samplingKernel_continuous (H : ℕ) : Continuous (samplingKernel H) := by
  unfold samplingKernel
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  exact continuous_finsetSum _ (fun r _ => samplingCharacter_continuous _)

theorem samplingKernel_expansion (H : ℕ) (t : ℝ) :
    (samplingKernel H t : ℂ) = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ q ∈ Finset.range H, samplingCharacter ((r : ℤ)-(q : ℤ)) t := by
  simp only [samplingKernel, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
    samplingCharacter_sub, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
  ring

theorem samplingKernel_integral (H : ℕ) (hH : 0 < H) :
    (∫ t, samplingKernel H t ∂unitIntervalMeasure) = 1 := by
  have hki : Integrable (samplingKernel H) unitIntervalMeasure :=
    (samplingKernel_continuous H).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hc : (∫ t, (samplingKernel H t : ℂ) ∂unitIntervalMeasure) = 1 := by
    simp_rw [samplingKernel_expansion]
    rw [integral_const_mul, integral_finsetSum _ (fun r _ =>
      integrable_finsetSum _ (fun q _ => samplingCharacter_integrable _))]
    simp_rw [integral_finsetSum _ (fun q _ => samplingCharacter_integrable _), samplingCharacter_integral]
    simp [sub_eq_zero, -Finset.mem_range, hH.ne']
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

end
end FiniteFactor

end OAI
