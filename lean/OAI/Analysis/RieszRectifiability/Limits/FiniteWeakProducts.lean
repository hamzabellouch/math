import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_smul_product {d k : ℕ}
    (μ : FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient k)) (c b : ℝ≥0) :
    (c • μ).prod (b • ν) = (c * b) • μ.prod ν := by
  apply Subtype.ext
  change (c • (μ : Measure (Ambient d))).prod (b • (ν : Measure (Ambient k))) =
    (c * b) • (μ : Measure (Ambient d)).prod (ν : Measure (Ambient k))
  simp only [← Measure.coe_nnreal_smul, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ENNReal.coe_mul, mul_comm]

theorem finiteMeasure_product_normalization {d k : ℕ}
    (μ : FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient k)) :
    μ.prod ν = (μ.mass * ν.mass) • (μ.normalize.prod ν.normalize).toFiniteMeasure := by
  calc
    _ = (μ.mass • μ.normalize.toFiniteMeasure).prod
        (ν.mass • ν.normalize.toFiniteMeasure) :=
      congrArg₂ FiniteMeasure.prod μ.self_eq_mass_smul_normalize ν.self_eq_mass_smul_normalize
    _ = _ := finiteMeasure_smul_product μ.normalize.toFiniteMeasure ν.normalize.toFiniteMeasure
      μ.mass ν.mass

theorem finiteMeasure_product_tendsto_nonzero {d k : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : ℕ → FiniteMeasure (Ambient k))
    (μ₀ : FiniteMeasure (Ambient d)) (ν₀ : FiniteMeasure (Ambient k))
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hν : Tendsto ν atTop (𝓝 ν₀))
    (hμ₀ : μ₀ ≠ 0) (hν₀ : ν₀ ≠ 0) :
    Tendsto (fun j => (μ j).prod (ν j)) atTop (𝓝 (μ₀.prod ν₀)) := by
  have hP := FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ₀
  have hQ := FiniteMeasure.tendsto_normalize_of_tendsto hν hν₀
  have hPQ : Tendsto (fun j => (μ j).normalize.prod (ν j).normalize) atTop
      (𝓝 (μ₀.normalize.prod ν₀.normalize)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ₀.normalize, ν₀.normalize)).comp (hP.prodMk_nhds hQ)
  have hF := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto
    (μ₀.normalize.prod ν₀.normalize)).comp hPQ
  have hm := hμ.mass.mul hν.mass
  have ht := hm.smul hF
  simpa only [Function.comp_apply, ← finiteMeasure_product_normalization] using! ht

theorem finiteMeasure_bounded_product_integral_tendsto {d k : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : ℕ → FiniteMeasure (Ambient k))
    (μ₀ : FiniteMeasure (Ambient d)) (ν₀ : FiniteMeasure (Ambient k))
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hν : Tendsto ν atTop (𝓝 ν₀))
    (hμ₀ : μ₀ ≠ 0) (hν₀ : ν₀ ≠ 0) (F : Ambient d × Ambient k →ᵇ ℝ) :
    Tendsto (fun j => ∫ q, F q ∂(μ j : Measure (Ambient d)).prod (ν j : Measure (Ambient k)))
      atTop (𝓝 (∫ q, F q ∂(μ₀ : Measure (Ambient d)).prod (ν₀ : Measure (Ambient k)))) :=
  FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (finiteMeasure_product_tendsto_nonzero μ ν μ₀ ν₀ hμ hν hμ₀ hν₀) F

end

end RieszRectifiability

end OAI
