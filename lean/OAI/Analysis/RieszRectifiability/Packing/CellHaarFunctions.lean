import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.NormalizedSetIndicators

namespace OAI

/-!
# Haar functions for nested cells

The difference of normalized indicators, scaled by the square root of the smaller cell's
mass, has mean zero. Its squared integral is the complementary mass ratio, and pairing
with an `L²` function recovers the difference of the two cell means.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

def cellHaar (μ : Measure X) (A B : Set X) (x : X) : ℝ :=
  Real.sqrt (μ.real A) * (normalizedSetIndicator μ A x - normalizedSetIndicator μ B x)

theorem cellHaar_memLp (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞) :
    MemLp (cellHaar μ A B) 2 μ :=
  ((normalizedSetIndicator_memLp μ A hA hAf).sub
    (normalizedSetIndicator_memLp μ B hB hBf)).const_mul (Real.sqrt (μ.real A))

theorem cellHaar_integrable (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞) :
    Integrable (cellHaar μ A B) μ :=
  ((normalizedSetIndicator_integrable μ A hA hAf).sub
    (normalizedSetIndicator_integrable μ B hB hBf)).const_mul (Real.sqrt (μ.real A))

theorem cellHaar_zero_of_notMem (μ : Measure X) (A B : Set X) (hAB : A ⊆ B)
    (x : X) (hx : x ∉ B) : cellHaar μ A B x = 0 := by
  rw [cellHaar, normalizedSetIndicator_of_notMem μ A x (fun h => hx (hAB h)),
    normalizedSetIndicator_of_notMem μ B x hx, sub_self, mul_zero]

theorem cellHaar_mean_zero (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (hAB : A ⊆ B) (hpos : 0 < μ.real A) : (∫ x, cellHaar μ A B x ∂μ) = 0 := by
  have hBpos : 0 < μ.real B := hpos.trans_le (measureReal_mono hAB hBf.ne)
  simp only [cellHaar]
  rw [integral_const_mul,
    integral_sub (normalizedSetIndicator_integrable μ A hA hAf)
      (normalizedSetIndicator_integrable μ B hB hBf),
    normalizedSetIndicator_integral μ A hA hpos,
    normalizedSetIndicator_integral μ B hB hBpos, sub_self, mul_zero]

theorem cellHaar_sq_integral (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (hAB : A ⊆ B) (hpos : 0 < μ.real A) :
    (∫ x, cellHaar μ A B x ^ 2 ∂μ) = 1 - μ.real A / μ.real B := by
  have hBpos : 0 < μ.real B := hpos.trans_le (measureReal_mono hAB hBf.ne)
  have ha := normalizedSetIndicator_memLp μ A hA hAf
  have hb := normalizedSetIndicator_memLp μ B hB hBf
  have hp : MemLp (fun x => normalizedSetIndicator μ A x * normalizedSetIndicator μ B x) 1 μ :=
    ha.mul hb
  simp only [cellHaar, mul_pow]
  rw [integral_const_mul, Real.sq_sqrt hpos.le,
    integral_squared_difference μ (normalizedSetIndicator μ A) (normalizedSetIndicator μ B)
      ha.integrable_sq (memLp_one_iff_integrable.mp hp) hb.integrable_sq,
    normalizedSetIndicator_sq_integral μ A hA hpos,
    normalizedSetIndicator_sq_integral μ B hB hBpos,
    normalizedSetIndicator_nested_product_integral μ A B hA hAB hpos]
  calc
    _ = μ.real A * (μ.real A)⁻¹ - μ.real A * (μ.real B)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ hpos.ne', div_eq_mul_inv]

theorem cellHaar_sq_integral_le_one (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (hAB : A ⊆ B) (hpos : 0 < μ.real A) : (∫ x, cellHaar μ A B x ^ 2 ∂μ) ≤ 1 := by
  rw [cellHaar_sq_integral μ A B hA hB hAf hBf hAB hpos]
  exact sub_le_self _ (div_nonneg measureReal_nonneg measureReal_nonneg)

theorem cellHaar_pairing (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    (∫ x, cellHaar μ A B x * u x ∂μ) =
      Real.sqrt (μ.real A) * (cellMean (μ.restrict A) u - cellMean (μ.restrict B) u) := by
  simp only [cellHaar, mul_assoc]
  rw [integral_const_mul, integral_mul_sub_eq μ (normalizedSetIndicator μ A)
    (normalizedSetIndicator μ B) u (normalizedSetIndicator_memLp μ A hA hAf)
      (normalizedSetIndicator_memLp μ B hB hBf) hu,
    normalizedSetIndicator_pairing μ A hA u, normalizedSetIndicator_pairing μ B hB u]

end

end RieszRectifiability

end OAI
