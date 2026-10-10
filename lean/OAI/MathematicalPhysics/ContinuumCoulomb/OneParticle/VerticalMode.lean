import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def verticalMode (freq z : ℝ) : ℝ :=
  Real.exp (-freq * z ^ 2 / 2) / Real.sqrt (Real.sqrt (Real.pi / freq))

theorem verticalMode_positive {freq : ℝ} (hfreq : 0 < freq) (z : ℝ) :
    0 < verticalMode freq z :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)))

theorem verticalMode_smooth (freq : ℝ) : ContDiff ℝ ∞ (verticalMode freq) := by
  unfold verticalMode
  fun_prop

theorem verticalMode_hasDerivAt (freq z : ℝ) :
    HasDerivAt (verticalMode freq) (-freq * z * verticalMode freq z) z := by
  have h := ((((hasDerivAt_id z).pow 2).const_mul (-freq)).div_const 2).exp
  convert h.div_const (Real.sqrt (Real.sqrt (Real.pi / freq))) using 1
  · rfl
  · simp only [verticalMode, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one]
    ring

theorem verticalMode_deriv (freq z : ℝ) :
    deriv (verticalMode freq) z = -freq * z * verticalMode freq z :=
  (verticalMode_hasDerivAt freq z).deriv

theorem verticalMode_second_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (verticalMode freq))
      ((freq ^ 2 * z ^ 2 - freq) * verticalMode freq z) z := by
  rw [show deriv (verticalMode freq) = (fun x => -freq * x * verticalMode freq x)
    from funext (verticalMode_deriv freq)]
  convert (((hasDerivAt_id z).const_mul (-freq)).mul (verticalMode_hasDerivAt freq z)) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem verticalMode_second_deriv (freq z : ℝ) :
    deriv (deriv (verticalMode freq)) z = (freq ^ 2 * z ^ 2 - freq) * verticalMode freq z :=
  (verticalMode_second_hasDerivAt freq z).deriv

theorem verticalMode_square {freq : ℝ} (_hfreq : 0 < freq) (z : ℝ) :
    verticalMode freq z ^ 2 = Real.exp (-freq * z ^ 2) / Real.sqrt (Real.pi / freq) := by
  unfold verticalMode
  rw [div_pow, Real.sq_sqrt (Real.sqrt_nonneg _), ← Real.exp_nat_mul]
  congr 2
  ring

theorem verticalMode_moment_integrable {freq : ℝ} (hfreq : 0 < freq) (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n * verticalMode freq z ^ 2) := by
  have h : Integrable (fun z : ℝ => z ^ n * Real.exp (-freq * z ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hfreq (s := (n : ℝ))
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)))
  simp_rw [verticalMode_square hfreq, ← mul_div_assoc]
  exact h.div_const _

theorem verticalMode_square_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun z : ℝ => verticalMode freq z ^ 2) := by
  simpa only [pow_zero, one_mul] using verticalMode_moment_integrable hfreq 0

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

theorem verticalMode_memLp {freq : ℝ} (hfreq : 0 < freq) : MemLp (verticalMode freq) 2 :=
  (memLp_two_iff_integrable_sq (verticalMode_smooth freq).continuous.aestronglyMeasurable).mpr
    (verticalMode_square_integrable hfreq)

theorem verticalMode_deriv_square_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun z : ℝ => deriv (verticalMode freq) z ^ 2) := by
  have h := (verticalMode_moment_integrable hfreq 2).const_mul (freq ^ 2)
  convert h using 1
  funext z
  rw [verticalMode_deriv]
  ring

theorem verticalMode_deriv_memLp {freq : ℝ} (hfreq : 0 < freq) :
    MemLp (deriv (verticalMode freq)) 2 := by
  apply (memLp_two_iff_integrable_sq ?_).mpr (verticalMode_deriv_square_integrable hfreq)
  exact ((verticalMode_smooth freq).continuous_deriv (by simp)).aestronglyMeasurable

end ContinuumCoulomb

end

end OAI
