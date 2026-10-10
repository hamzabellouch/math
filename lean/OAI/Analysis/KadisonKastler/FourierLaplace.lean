import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! # Fourier transform of the two-sided exponential

This scalar calculation is the first half of the Cauchy-kernel character
formula needed for Poisson demodulation. It uses the existing half-line
exponential integrals and no additional published-input hypothesis.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The integrable two-sided exponential, with complex values. -/
def laplaceKernel (a t : ℝ) : ℂ := Complex.exp (-((a : ℂ) * ((|t| : ℝ) : ℂ)))

private def laplaceFourierIntegrand (a ξ t : ℝ) : ℂ :=
  Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * laplaceKernel a t

private theorem laplaceFourierIntegrand_nonpos (a ξ t : ℝ) (ht : t ≤ 0) :
    laplaceFourierIntegrand a ξ t =
      Complex.exp (((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
  unfold laplaceFourierIntegrand laplaceKernel
  rw [abs_of_nonpos ht, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem laplaceFourierIntegrand_nonneg (a ξ t : ℝ) (ht : 0 ≤ t) :
    laplaceFourierIntegrand a ξ t =
      Complex.exp ((-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
  unfold laplaceFourierIntegrand laplaceKernel
  rw [abs_of_nonneg ht, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem laplaceFourierIntegrand_integrableOn_left {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    IntegrableOn (laplaceFourierIntegrand a ξ) (Set.Iic 0) := by
  have hpos : 0 < ((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I).re := by
    simpa using ha
  apply (integrableOn_exp_mul_complex_Iic hpos 0).congr_fun
  · intro t ht
    exact (laplaceFourierIntegrand_nonpos a ξ t ht).symm
  · exact measurableSet_Iic

private theorem laplaceFourierIntegrand_integrableOn_right {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    IntegrableOn (laplaceFourierIntegrand a ξ) (Set.Ioi 0) := by
  have hneg : (-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I).re < 0 := by
    simpa using (neg_lt_zero.mpr ha)
  apply (integrableOn_exp_mul_complex_Ioi hneg 0).congr_fun
  · intro t ht
    exact (laplaceFourierIntegrand_nonneg a ξ t ht.le).symm
  · exact measurableSet_Ioi

/-- The transform is the sum of the two elementary half-line resolvents. -/
theorem fourier_laplaceKernel_resolvents {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (laplaceKernel a) ξ =
      ((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ -
        (-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ t : ℝ, laplaceFourierIntegrand a ξ t) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi (laplaceFourierIntegrand_integrableOn_left ha ξ)
    (laplaceFourierIntegrand_integrableOn_right ha ξ)]
  have hleft : (∫ t in Set.Iic (0 : ℝ), laplaceFourierIntegrand a ξ t) =
      ((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
    calc
      _ = ∫ t in Set.Iic (0 : ℝ),
          Complex.exp (((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact laplaceFourierIntegrand_nonpos a ξ t ht
      _ = _ := by
        rw [integral_exp_mul_complex_Iic (by simpa using ha)]
        simp
  have hright : (∫ t in Set.Ioi (0 : ℝ), laplaceFourierIntegrand a ξ t) =
      - (-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ),
          Complex.exp ((-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact laplaceFourierIntegrand_nonneg a ξ t ht.le
      _ = _ := by
        rw [integral_exp_mul_complex_Ioi (by simpa using (neg_lt_zero.mpr ha))]
        simp [div_eq_mul_inv]
  simp only [hleft, hright, sub_eq_add_neg]

end

/-- Integrability of the two-sided exponential, obtained from the same
half-line estimates used in its transform calculation. -/
theorem integrable_laplaceKernel {a : ℝ} (ha : 0 < a) : Integrable (laplaceKernel a) := by
  have hl := laplaceFourierIntegrand_integrableOn_left ha 0
  have hr := laplaceFourierIntegrand_integrableOn_right ha 0
  have h := hl.union hr
  have he : laplaceFourierIntegrand a 0 = laplaceKernel a := by
    funext t
    simp [laplaceFourierIntegrand]
  rw [he] at h
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h

theorem continuous_laplaceKernel (a : ℝ) : Continuous (laplaceKernel a) := by
  unfold laplaceKernel
  fun_prop

private theorem complex_resolvent_pair {a b : ℝ} (ha : 0 < a) :
    ((a : ℂ) - (b : ℂ) * Complex.I)⁻¹ - (-(a : ℂ) - (b : ℂ) * Complex.I)⁻¹ =
      ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hminus : (a : ℂ) - (b : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hh
    exact ha.ne' hh
  have hplus : (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hh
    exact ha.ne' hh
  have hn : -(a : ℂ) - (b : ℂ) * Complex.I = -((a : ℂ) + (b : ℂ) * Complex.I) := by ring
  rw [hn, inv_neg, sub_neg_eq_add]
  push_cast
  have hp : ((a : ℂ) - (b : ℂ) * Complex.I) *
      ((a : ℂ) + (b : ℂ) * Complex.I) = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    calc
      _ = (a : ℂ) ^ 2 - (b : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [← hp]
  field_simp [hminus, hplus]
  ring

/-- The scalar rational form of the Fourier transform. -/
theorem fourier_laplaceKernel {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (laplaceKernel a) ξ = ((2 * a / (a ^ 2 + (2 * Real.pi * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [fourier_laplaceKernel_resolvents ha]
  exact complex_resolvent_pair ha

end KadisonKastler

end OAI
