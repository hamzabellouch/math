import OAI.Analysis.CircleDomains.Probability.PublishedMeasureDuality
import OAI.Analysis.CircleDomains.Modulus.CostPerturbation

namespace OAI

/-! Passing a pointwise lower bound for every admissible metric to the
measure-family modulus. The metrics retain extended values. -/

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {A Z : Type*} [MeasurableSpace Z]

theorem le_modulus_of_admissible_norm_bound
    (σ : Measure Z) (K : A → FiniteMeasure Z) (c : ℝ≥0∞)
    (hbound : ∀h : Z → ℝ≥0∞, Measurable h →
      (∀a, 1 ≤ ∫⁻z, h z ∂(K a : Measure Z)) → c ≤ squareIntegralNorm σ h) :
    c ^ 2 ≤ measureFamilyModulus A Z σ K := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro hadm
  have hb := pow_le_pow_left' (hbound h hh hadm) 2
  have he : (squareIntegralNorm σ h) ^ 2 = ∫⁻z, h z ^ 2 ∂σ := by
    rw [squareIntegralNorm, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  exact hb.trans_eq he

end CircleDomainRigidity

end

end OAI
