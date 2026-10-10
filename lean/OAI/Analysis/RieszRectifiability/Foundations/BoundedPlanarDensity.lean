import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.GrowthVolumeDomination

namespace OAI

/-!
# Bounded densities for measures supported on planes

Domination by a scalar multiple of a reference measure bounds the
Radon–Nikodym derivative and gives a measurable, everywhere bounded density.
Intrinsic upper growth applies this construction to Euclidean volume and to
measures supported on the range of a linear isometry.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem rnDeriv_le_of_nnreal_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite ν] (c : ℝ≥0) (hdom : μ ≤ c • ν) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ (c : ℝ≥0∞) := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s _hs _hfin
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.coe_nnreal_smul_apply] using!
    (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (hdom s)

theorem exists_bounded_density_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (c : ℝ≥0) (hdom : μ ≤ c • ν) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ c) ∧
      ν.withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  let f : α → ℝ := fun x => min (c : ℝ) (μ.rnDeriv ν x).toReal
  have hm : Measurable f := measurable_const.min (μ.measurable_rnDeriv ν).ennreal_toReal
  have heq : (fun x => ENNReal.ofReal (f x)) =ᵐ[ν] μ.rnDeriv ν := by
    filter_upwards [rnDeriv_le_of_nnreal_domination μ ν c hdom] with x hx
    have hne : μ.rnDeriv ν x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hx
    have hreal : (μ.rnDeriv ν x).toReal ≤ (c : ℝ) := by
      simpa only [ENNReal.coe_toReal] using! (ENNReal.toReal_le_toReal hne ENNReal.coe_ne_top).mpr hx
    change ENNReal.ofReal (min (c : ℝ) (μ.rnDeriv ν x).toReal) = μ.rnDeriv ν x
    rw [min_eq_right hreal, ENNReal.ofReal_toReal hne]
  refine ⟨f, hm, fun x => ⟨le_min c.coe_nonneg ENNReal.toReal_nonneg, min_le_left _ _⟩, ?_⟩
  rw [withDensity_congr_ae heq]
  exact Measure.withDensity_rnDeriv_eq μ ν
    (hdom.absolutelyContinuous.trans Measure.smul_absolutelyContinuous)

theorem exists_bounded_intrinsic_density (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient n)) (hg : GlobalUpperGrowth n C μ) :
    ∃ f : Ambient n → ℝ, Measurable f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n C) ∧
      (volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts C μ hg
  exact exists_bounded_density_of_domination μ volume (intrinsicGrowthDensityBound n C)
    (intrinsic_growth_le_volume n C μ hg)

theorem exists_bounded_planar_density {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d))
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hg : GlobalUpperGrowth n C ν) :
    ∃ f : Ambient n → ℝ, Measurable f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n C) ∧
      ((volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x))).map L = ν := by
  obtain ⟨f, hm, hb, heq⟩ := exists_bounded_intrinsic_density n C
    (planarPullbackMeasure L ν) (planarPullbackMeasure_growth L ν hs C hg)
  refine ⟨f, hm, hb, ?_⟩
  rw [heq]
  exact planarPullbackMeasure_recover L ν hs

end

end RieszRectifiability

end OAI
