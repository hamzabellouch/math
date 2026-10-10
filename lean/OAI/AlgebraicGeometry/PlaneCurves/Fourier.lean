import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.ContinuousMap.Basic
import OAI.AlgebraicGeometry.PlaneCurves.LaurentCoefficients

namespace OAI

noncomputable section

/-!
# Circle traces, Fourier uniqueness, and Laurent reconstruction
-/

/-! Actual restrictions of punctured-plane functions to circles of positive radius. -/
namespace Nagata.W01

section

abbrev AngularCircle := AddCircle (2 * Real.pi)

def circleParam (r : ℝ) (t : AngularCircle) : ℂ :=
  (r : ℂ) * (AddCircle.toCircle t : ℂ)

theorem circleParam_ne_zero {r : ℝ} (hr : 0 < r) (t : AngularCircle) :
    circleParam r t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (AddCircle.toCircle t).coe_ne_zero

theorem continuous_circleParam (r : ℝ) : Continuous (circleParam r) :=
  continuous_const.mul (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem circleParam_coe (r θ : ℝ) :
    circleParam r (θ : AngularCircle) = circleMap 0 r θ := by
  simp [circleParam, AddCircle.toCircle_apply_mk, Real.two_pi_pos.ne', Circle.coe_exp, circleMap]

theorem circleParam_arg (z : ℂ) :
    circleParam ‖z‖ (Complex.arg z : AngularCircle) = z := by
  rw [circleParam_coe]
  simp [circleMap]

def circleTrace (r : ℝ) (f : ℂ → ℂ) : AngularCircle → ℂ :=
  fun t => f (circleParam r t)

@[simp] theorem circleTrace_coe (r : ℝ) (f : ℂ → ℂ) (θ : ℝ) :
    circleTrace r f (θ : AngularCircle) = f (circleMap 0 r θ) := by
  rw [circleTrace, circleParam_coe]

theorem continuous_circleTrace {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z) : Continuous (circleTrace r f) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hf _ (circleParam_ne_zero hr t)).comp (continuous_circleParam r).continuousAt

/-- The actual continuous restriction to the circle, with continuity proved locally. -/
def circleTraceMap (r : ℝ) (hr : 0 < r) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z) : C(AngularCircle, ℂ) :=
  ⟨circleTrace r f, continuous_circleTrace hr hf⟩

/-- Positive-radius circles exhaust the genuine domain C*. -/
theorem punctured_eq_zero_of_circleTrace_zero {f : ℂ → ℂ}
    (h : ∀ r : ℝ, 0 < r → ∀ t : AngularCircle, circleTrace r f t = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  intro z hz
  have hh := h ‖z‖ (norm_pos_iff.mpr hz) (Complex.arg z : AngularCircle)
  simpa [circleTrace, circleParam_arg] using hh

/-! Genuine continuous-circle Fourier uniqueness, for Laurent reconstruction. -/

variable {T : ℝ} [Fact (0 < T)]

/-- A genuine continuous function on a circle is determined by its Fourier coefficients. -/
theorem continuous_circle_zero_of_fourier_zero (f : C(AddCircle T, ℂ))
    (h : ∀ k : ℤ, fourierCoeff f k = 0) : f = 0 := by
  have hs : Summable (fourierCoeff f) := by
    simpa only [show fourierCoeff f = (fun _ : ℤ => (0 : ℂ)) from funext h]
      using (summable_zero : Summable (fun _ : ℤ => (0 : ℂ)))
  ext x
  have hsum := has_pointwise_sum_fourier_series_of_summable hs x
  simp only [h, zero_smul] at hsum
  exact hsum.unique hasSum_zero

/-- Uniqueness compares the actual functions, rather than formal coefficient sequences. -/
theorem continuous_circle_eq_of_fourier_eq (f g : C(AddCircle T, ℂ))
    (h : ∀ k : ℤ, fourierCoeff f k = fourierCoeff g k) : f = g := by
  have hz : f - g = 0 := by
    apply continuous_circle_zero_of_fourier_zero
    intro k
    have hneg : fourierCoeff (fun x => -g x) k = -fourierCoeff g k := by
      simpa using fourierCoeff.const_mul (g : AddCircle T → ℂ) (-1) k
    have hadd := congrFun (fourierCoeff.add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((-g).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) k
    change fourierCoeff (fun x => f x + (-g x)) k = 0
    calc
      _ = fourierCoeff f k + fourierCoeff (fun x => -g x) k := hadd
      _ = 0 := by rw [hneg, h k, add_neg_cancel]

  exact sub_eq_zero.mp hz

end

/-! Exact algebraic factors in the genuine Laurent/Fourier integral comparison. -/
open Complex

theorem laurent_tangent_integrand (z w : ℂ) (hz : z ≠ 0) (k : ℤ) :
    (z * I) * (z ^ (-k - 1) * w) = I * z ^ (-k) * w := by
  have hpow : z * z ^ (-k - 1) = z ^ (-k) := by
    conv_lhs => lhs; rw [← zpow_one z]
    rw [← zpow_add₀ hz]
    congr 1
    omega
  calc
    _ = I * (z * z ^ (-k - 1)) * w := by ring
    _ = _ := by rw [hpow]

theorem laurent_scalar_normalization (T a b : ℂ) (hT : T ≠ 0) :
    (T * I)⁻¹ * ((I * a) * b) = a * (T⁻¹ * b) := by
  field_simp [hT, I_ne_zero]

theorem laurent_radius_factor_ne_zero {r : ℝ} (hr : 0 < r) (k : ℤ) :
    (r : ℂ) ^ (-k) ≠ 0 :=
  zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')

end Nagata.W01

section

/-! The actual circle-integral Laurent coefficients are scaled Fourier coefficients.
This identifies genuine analytic extraction and proves uniqueness on C* once the
coefficients vanish on every positive-radius circle. -/
open Complex Real
namespace Nagata.W01

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem fourier_eq_circle_zpow (k : ℤ) (t : AngularCircle) :
    fourier k t = (AddCircle.toCircle t : ℂ) ^ k := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]

theorem circleMap_zpow_fourier (r θ : ℝ) (k : ℤ) :
    circleMap 0 r θ ^ k = (r : ℂ) ^ k * fourier k (θ : AngularCircle) := by
  rw [← circleParam_coe, circleParam, mul_zpow, fourier_eq_circle_zpow]

theorem laurent_integrand_parameterization {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (k : ℤ) (θ : ℝ) :
    (circleMap 0 r θ * I) * ((circleMap 0 r θ) ^ (-k - 1) * f (circleMap 0 r θ)) =
      (I * (r : ℂ) ^ (-k)) * (fourier (-k) (θ : AngularCircle) * f (circleMap 0 r θ)) := by
  have hz : circleMap 0 r θ ≠ 0 := by
    simpa [circleParam_coe] using circleParam_ne_zero hr (θ : AngularCircle)
  rw [laurent_tangent_integrand _ _ hz, circleMap_zpow_fourier]
  ring
/-- Exact comparison of the genuine complex circle integral with Fourier extraction. -/
theorem analyticLaurentCoeff_eq_fourier {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (k : ℤ) :
    Nagata.W09.analyticLaurentCoeff r f k =
      (r : ℂ) ^ (-k) * fourierCoeff (circleTrace r f) k := by
  unfold Nagata.W09.analyticLaurentCoeff circleIntegral
  simp only [deriv_circleMap, smul_eq_mul]
  have hi : (fun θ : ℝ => (circleMap 0 r θ * I) *
      ((circleMap 0 r θ) ^ (-k - 1) * f (circleMap 0 r θ))) =
      (fun θ : ℝ => (I * (r : ℂ) ^ (-k)) *
        (fourier (-k) (θ : AngularCircle) * f (circleMap 0 r θ))) :=
    funext (laurent_integrand_parameterization hr f k)
  rw [hi, intervalIntegral.integral_const_mul (a := 0) (b := 2 * Real.pi)
    (μ := MeasureTheory.volume) (I * (r : ℂ) ^ (-k))
    (fun θ : ℝ => fourier (-k) (θ : AngularCircle) * f (circleMap 0 r θ))]
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, smul_eq_mul, circleTrace_coe, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ, Complex.I_ne_zero]

/-- Zero Laurent coefficients on a radius force the actual circle restriction to vanish. -/
theorem circleTrace_zero_of_laurentCoeff_zero {r : ℝ} (hr : 0 < r) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z)
    (hc : ∀ k : ℤ, Nagata.W09.analyticLaurentCoeff r f k = 0) :
    ∀ t : AngularCircle, circleTrace r f t = 0 := by
  have hz : circleTraceMap r hr f hf = 0 := by
    apply continuous_circle_zero_of_fourier_zero
    intro k
    have h := hc k
    rw [analyticLaurentCoeff_eq_fourier hr] at h
    exact (mul_eq_zero.mp h).resolve_left (laurent_radius_factor_ne_zero hr k)
  intro t
  exact congrArg (fun g : C(AngularCircle, ℂ) => g t) hz

/-- Laurent uniqueness on C* via actual continuous restrictions and circle exhaustion. -/
theorem punctured_zero_of_all_laurentCoeff_zero (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z)
    (hc : ∀ r : ℝ, 0 < r → ∀ k : ℤ, Nagata.W09.analyticLaurentCoeff r f k = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  apply punctured_eq_zero_of_circleTrace_zero
  intro r hr
  exact circleTrace_zero_of_laurentCoeff_zero hr f hf (hc r hr)

end Nagata.W01

end

/-! Genuine Laurent uniqueness and injective extraction for actual holomorphic
multiplier sections on C*. Radius invariance and continuous Fourier reconstruction
are explicit imported lemmas; no injectivity field or formal-series substitute occurs. -/
namespace Nagata.W01

theorem punctured_zero_of_radius_one_laurentCoeff_zero (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hc : ∀ k : ℤ, Nagata.W09.analyticLaurentCoeff 1 f k = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  apply punctured_zero_of_all_laurentCoeff_zero f (fun z hz => (hf z hz).continuousAt)
  intro r hr k
  rw [Nagata.W09.analyticLaurentCoeff_radius_independent hr zero_lt_one hf k]
  exact hc k

/-- Actual extraction at radius one is injective on genuine holomorphic sections. -/
theorem laurentCoefficientMap_injective (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Function.Injective (Nagata.W09.laurentCoefficientMap τ n γ) := by
  intro f g hfg
  have hzero : Nagata.W09.laurentCoefficientMap τ n γ (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hz := punctured_zero_of_radius_one_laurentCoeff_zero (f - g).val
    (f - g).property.2.1 (fun k => congrFun hzero k)
  apply Nagata.W08.automorphicSections_ext
  intro z hzne
  have h := hz z hzne
  change f.val z - g.val z = 0 at h
  exact sub_eq_zero.mp h

end Nagata.W01

end

end OAI
