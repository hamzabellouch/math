import OAI.Analysis.RCDHeat.HeatTest

namespace OAI

/-! # Probability laws on a measurable compact support

The subtype law has the exact normalized restriction as its ambient law,
and an explicit bounded nonnegative density. Compactness is supplied only
where the heat-factor construction uses it.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem restricted_probability_law (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (hS0 : μ S ≠ 0) (hSf : μ S ≠ ∞) :
    ∃ (ν : Measure S) (ρ : X → ℝ) (B : ℝ≥0), IsProbabilityMeasure ν ∧
      ν.map Subtype.val = uniformOn μ S ∧ Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ x, |ρ x| ≤ B) ∧
      ν.map Subtype.val = μ.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  let m := uniformOn μ S
  let := uniformOn_probability μ S hS0 hSf
  have hs : ∀ᵐ x ∂m, x ∈ S := uniformOn_ae_mem μ S hS
  let ν : Measure S := m.comap Subtype.val
  have hprob : IsProbabilityMeasure ν :=
    (MeasurableEmbedding.subtype_coe hS).isProbabilityMeasure_comap (by
      simpa only [Subtype.range_coe] using hs)
  have hmap : ν.map Subtype.val = m := by
    rw [show ν = m.comap Subtype.val from rfl,map_comap_subtype_coe hS]
    exact Measure.restrict_eq_self_of_ae_mem hs
  let c : ℝ := (μ.real S)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr measureReal_nonneg
  let ρ : X → ℝ := S.indicator (fun _ => c)
  have hmρ : Measurable ρ := measurable_const.indicator hS
  have hpρ (x : X) : 0 ≤ ρ x := by
    by_cases hx : x ∈ S <;> simp [ρ,hx,hc]
  have hbρ (x : X) : |ρ x| ≤ (⟨c,hc⟩ : ℝ≥0) := by
    rw [abs_of_nonneg (hpρ x)]
    by_cases hx : x ∈ S <;> simp [ρ,hx,hc]
  refine ⟨ν,ρ,⟨c,hc⟩,hprob,hmap,hmρ,hpρ,hbρ,?_⟩
  rw [hmap]
  have he : (fun x => ENNReal.ofReal (ρ x)) = S.indicator (fun _ => (μ S)⁻¹) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [ρ,Set.indicator_of_mem hx,c,measureReal_def]
      rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hS0 hSf),ENNReal.ofReal_toReal hSf]
    · simp [ρ,hx]
  rw [he,withDensity_indicator hS,withDensity_const]
  rfl

theorem restricted_law_integral {S : Set X} (μ : Measure X) (ν : Measure S)
    (hν : ν.map Subtype.val = uniformOn μ S) (f : X → ℝ) (hf : Measurable f) :
    (∫ a : S, f a ∂ν) = (μ.real S)⁻¹*(∫ x in S, f x ∂μ) := by
  rw [← integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,hν]
  simp only [uniformOn,integral_smul_measure,ENNReal.toReal_inv,measureReal_def,smul_eq_mul]

end RegularPointCoordinates

end

end OAI
