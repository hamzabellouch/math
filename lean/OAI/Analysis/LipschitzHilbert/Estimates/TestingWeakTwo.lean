import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! Recover a weak-L2 distribution bound from the restricted L1 testing
inequality. Integrability supplies finiteness of the testing level set. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem weak_two_of_testing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (A : ℝ) (hA : 0 ≤ A)
    (htest : ∀ Q : Set Ω, MeasurableSet Q → μ Q ≠ ∞ →
      (∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (A*Real.sqrt (μ.real Q)))
    (t : ℝ) (ht : 0 < t) :
    μ {x | t < f x} ≤ ENNReal.ofReal (A^2/t^2) := by
  let Q := {x | t < f x}
  have hQ : MeasurableSet Q := measurableSet_lt measurable_const hf
  have hfin : μ Q ≠ ∞ := (hfi.measure_gt_lt_top ht).ne
  have hlo : ENNReal.ofReal t * μ Q ≤ ∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ := by
    calc
      _ = ∫⁻ _x in Q, ENNReal.ofReal t ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hQ (fun _ hx => ENNReal.ofReal_le_ofReal hx.le)
  have hle := hlo.trans (htest Q hQ hfin)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (mul_nonneg hA (Real.sqrt_nonneg _))] at hr
  change t * μ.real Q ≤ A * Real.sqrt (μ.real Q) at hr
  have hm : 0 ≤ μ.real Q := measureReal_nonneg
  have hs : t*Real.sqrt (μ.real Q) ≤ A := by
    by_cases hz : μ.real Q = 0
    · simpa [hz] using hA
    · have hx : 0 < Real.sqrt (μ.real Q) := Real.sqrt_pos.mpr (lt_of_le_of_ne hm (Ne.symm hz))
      apply (mul_le_mul_iff_right₀ hx).mp
      nlinarith [Real.sq_sqrt hm]
  have hs2 : t^2*μ.real Q ≤ A^2 := by
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t*Real.sqrt (μ.real Q)) hs
    nlinarith [Real.sq_sqrt hm]
  have hreal : μ.real Q ≤ A^2/t^2 := (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith)
  change μ Q ≤ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

end LipschitzHilbert

end

end OAI
