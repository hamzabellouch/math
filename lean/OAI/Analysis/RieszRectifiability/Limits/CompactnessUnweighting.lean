import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence
import OAI.Analysis.RieszRectifiability.Limits.CompactnessWeightedMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

def compactnessUnweightedMeasure {d : ℕ} (n : ℕ) (ν : Measure (Ambient d)) :
    Measure (Ambient d) := ν.withDensity (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹))

theorem compactnessWeight_inv_continuous {d : ℕ} (n : ℕ) :
    Continuous (fun x : Ambient d => (compactnessWeight n x)⁻¹) :=
  (compactnessWeight_continuous n).inv₀ (fun x => ne_of_gt (compactnessWeight_pos n x))

theorem compactnessUnweightedMeasure_locally_finite {d : ℕ} (n : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (compactnessUnweightedMeasure n ν) := by
  constructor
  intro K hK
  have hi : IntegrableOn (fun x => (compactnessWeight n x)⁻¹) K ν :=
    ContinuousOn.integrableOn_compact hK (compactnessWeight_inv_continuous n).continuousOn
  rw [compactnessUnweightedMeasure, withDensity_apply _ hK.measurableSet,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x =>
      inv_nonneg.mpr (compactnessWeight_pos n x).le))]
  exact ENNReal.ofReal_lt_top

theorem compactness_unweight_weight {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) :
    compactnessUnweightedMeasure n (compactnessWeightedMeasure n μ) = μ := by
  rw [compactnessUnweightedMeasure, compactnessWeightedMeasure,
    ← withDensity_mul μ (compactnessWeight_continuous n).measurable.ennreal_ofReal
      (compactnessWeight_inv_continuous n).measurable.ennreal_ofReal]
  have heq : (fun x : Ambient d => ENNReal.ofReal (compactnessWeight n x)) *
      (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹)) = 1 := by
    funext x
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (compactnessWeight_pos n x).le,
      mul_inv_cancel₀ (ne_of_gt (compactnessWeight_pos n x)), ENNReal.ofReal_one, Pi.one_apply]
  rw [heq, withDensity_one]

theorem compactnessUnweightedMeasure_integral {d : ℕ} (n : ℕ)
    (ν : Measure (Ambient d)) (f : Ambient d → ℝ) :
    (∫ x, f x ∂compactnessUnweightedMeasure n ν) =
      ∫ x, (compactnessWeight n x)⁻¹ * f x ∂ν := by
  rw [compactnessUnweightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (compactnessWeight_inv_continuous n).measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (ENNReal.ofReal ((compactnessWeight n x)⁻¹)).toReal • f x =
      (compactnessWeight n x)⁻¹ * f x
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (compactnessWeight_pos n x).le), smul_eq_mul])

theorem compactness_unweight_weak_convergence {d : ℕ} (n : ℕ)
    (νj : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hν : Tendsto νj atTop (𝓝 ν)) :
    CompactTestConvergence (fun j => compactnessUnweightedMeasure n (νj j : Measure (Ambient d)))
      (compactnessUnweightedMeasure n (ν : Measure (Ambient d))) := by
  intro f
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => (compactnessWeight n x)⁻¹ * f x,
      (compactnessWeight_inv_continuous n).mul f.continuous⟩, f.hasCompactSupport.mul_left⟩
  have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν test.toBoundedContinuousFunction
  change Tendsto (fun j => ∫ x, (compactnessWeight n x)⁻¹ * f x ∂(νj j : Measure (Ambient d)))
    atTop (𝓝 (∫ x, (compactnessWeight n x)⁻¹ * f x ∂(ν : Measure (Ambient d)))) at h
  simpa only [compactnessUnweightedMeasure_integral] using! h

theorem compactness_weighted_limit_gives_original_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hg : ∀ j, GlobalUpperGrowth n C (μ j)) (ν : FiniteMeasure (Ambient d))
    (hν : Tendsto (fun j => compactnessFiniteMeasure n (μ j) C (hg j)) atTop (𝓝 ν)) :
    CompactTestConvergence μ (compactnessUnweightedMeasure n ν) := by
  have h := compactness_unweight_weak_convergence n _ ν hν
  simpa only [compactnessFiniteMeasure, FiniteMeasure.toMeasure_mk, compactness_unweight_weight] using! h

end

end RieszRectifiability

end OAI
