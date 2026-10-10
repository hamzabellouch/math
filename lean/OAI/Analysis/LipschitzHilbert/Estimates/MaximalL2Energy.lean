import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The p=2 maximal energy argument. A localized weak-L1 estimate,
layer cake, and Cauchy--Schwarz give the strong L2 constant four. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem maximal_square_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H g : Ω → ℝ) (hH : Measurable H) (hg : Measurable g)
    (hH0 : ∀ x, 0 ≤ H x) (hg0 : ∀ x, 0 ≤ g x)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t*μ {x | t ≤ H x} ≤
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal ((H x)^2) ∂μ) ≤
      2 * ∫⁻ x, ENNReal.ofReal (g x*H x) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hν (t : ℝ) : ν {x | t ≤ H x} =
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ :=
    withDensity_apply _ (measurableSet_le measurable_const hH)
  have hpow := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hH0) hH.aemeasurable (by norm_num : (0:ℝ)<2)
  simp only [Real.rpow_two, show (2:ℝ)-1=1 by norm_num, Real.rpow_one,
    ENNReal.ofReal_ofNat] at hpow
  rw [hpow]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ν {x | t ≤ H x} := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      rw [hν, mul_comm]
      exact hweak t ht
    _ = ∫⁻ x, ENNReal.ofReal (H x) ∂ν :=
      (lintegral_eq_lintegral_meas_le ν (Filter.Eventually.of_forall hH0) hH.aemeasurable).symm
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul μ hg.ennreal_ofReal hH.ennreal_ofReal]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (hg0 x)).symm

theorem maximal_L2_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H g : Ω → ℝ) (hH : Measurable H) (hg : Measurable g)
    (hH0 : ∀ x, 0 ≤ H x) (hg0 : ∀ x, 0 ≤ g x)
    (hH2 : MemLp H 2 μ) (hg2 : MemLp g 2 μ)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t*μ {x | t ≤ H x} ≤
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ) :
    (∫ x, (H x)^2 ∂μ) ≤ 4 * ∫ x, (g x)^2 ∂μ := by
  have hintH := hH2.integrable_sq
  have hintg := hg2.integrable_sq
  have hintprod : Integrable (fun x => g x*H x) μ := hg2.integrable_mul hH2
  have h := maximal_square_lintegral μ H g hH hg hH0 hg0 hweak
  rw [← ofReal_integral_eq_lintegral_ofReal hintH
    (Filter.Eventually.of_forall (fun x => sq_nonneg (H x))),
    ← ofReal_integral_eq_lintegral_ofReal hintprod
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hg0 x) (hH0 x)))] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg (H x))),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => mul_nonneg (hg0 x) (hH0 x)))] at hr
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall hg0)
    (Filter.Eventually.of_forall hH0) (by simpa using hg2) (by simpa using hH2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hposH : 0 ≤ ∫ x, (H x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (H x))
  have hposg : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (g x))
  have hrootH := Real.sq_sqrt hposH
  have hrootg := Real.sq_sqrt hposg
  have hsquare := sq_nonneg (Real.sqrt (∫ x, (H x)^2 ∂μ) -
    2*Real.sqrt (∫ x, (g x)^2 ∂μ))
  nlinarith [Real.sqrt_nonneg (∫ x, (H x)^2 ∂μ), Real.sqrt_nonneg (∫ x, (g x)^2 ∂μ)]

end LipschitzHilbert

end

end OAI
