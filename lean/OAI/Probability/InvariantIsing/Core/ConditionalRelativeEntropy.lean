import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! Exact relative entropy of conditioning on a nonnull event. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set

namespace InvariantIsing

theorem conditioned_measure_entropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (S : Set X) (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    klDiv (cond μ S) μ ≠ ⊤ ∧ (klDiv (cond μ S) μ).toReal = -Real.log (μ.real S) := by
  let ν := cond μ S
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hpos
  have hν : ν ≪ μ := cond_absolutelyContinuous
  have hνr : ν ≪ μ.restrict S := Measure.smul_absolutelyContinuous
  have hs := hνr.ae_le (llr_smul_left (show μ.restrict S ≪ μ from Measure.restrict_le_self.absolutelyContinuous)
    (μ S)⁻¹ (ENNReal.inv_ne_zero.mpr (measure_ne_top μ S)) (ENNReal.inv_ne_top.mpr hpos))
  have hr := hν.ae_le (Measure.rnDeriv_restrict_self μ hS)
  have hl : llr ν μ =ᵐ[ν] fun _ => -Real.log (μ.real S) := by
    filter_upwards [hs, hr, ae_cond_mem hS (μ := μ)] with x hx hx' hxS
    change llr ((μ S)⁻¹ • μ.restrict S) μ x = _
    rw [hx]
    change Real.log ((μ.restrict S).rnDeriv μ x).toReal + Real.log ((μ S)⁻¹).toReal = _
    rw [hx', Set.indicator_of_mem hxS]
    simp only [Pi.one_apply, ENNReal.toReal_one, Real.log_one, zero_add,
      ENNReal.toReal_inv, Real.log_inv, measureReal_def]
  have hi : Integrable (llr ν μ) ν := (integrable_const _).congr hl.symm
  refine ⟨klDiv_ne_top hν hi, ?_⟩
  rw [toReal_klDiv hν hi, integral_congr_ae hl]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, add_sub_cancel_right]

end InvariantIsing

end

end OAI
