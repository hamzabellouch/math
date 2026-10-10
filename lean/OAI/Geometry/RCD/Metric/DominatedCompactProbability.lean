import OAI.Geometry.RCD.Metric.BoundedFiniteDensity
import OAI.Geometry.RCD.Sobolev.CompactRestrictedLaw

namespace OAI

/-! # Subtype laws and bounded densities for dominated supported probabilities -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem dominated_probability_density (μ ν : Measure X) [SigmaFinite μ] [IsProbabilityMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) :
    ∃ (ρ : X → ℝ) (B : ℝ≥0), Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ᵐ x ∂μ, |ρ x| ≤ B) ∧ ν=μ.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  let ρ := fun x => (ν.rnDeriv μ x).toReal
  let B : ℝ≥0 := ⟨C.toReal,ENNReal.toReal_nonneg⟩
  have hr : ν.rnDeriv μ ≤ᵐ[μ] fun _ => C := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ν.measurable_rnDeriv μ)
    intro A _ _
    have hh := (Measure.setLIntegral_rnDeriv_le (μ := ν) (ν := μ) A).trans (hν A)
    simpa only [lintegral_const,Measure.restrict_apply_univ,Measure.smul_apply,smul_eq_mul] using hh
  refine ⟨ρ,B,(ν.measurable_rnDeriv μ).ennreal_toReal,fun _ => ENNReal.toReal_nonneg,?_,?_⟩
  · filter_upwards [hr] with x hx
    rw [abs_of_nonneg (ENNReal.toReal_nonneg (a := ν.rnDeriv μ x))]
    exact ENNReal.toReal_mono hC hx
  · rw [← Measure.withDensity_rnDeriv_eq ν μ (Measure.absolutelyContinuous_of_le_smul hν)]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx
    exact (ENNReal.ofReal_toReal hx).symm

theorem dominated_supported_probability_law (μ ν : Measure X)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (S : Set X) (hS : MeasurableSet S)
    (hs : ∀ᵐ x ∂ν, x ∈ S) {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) :
    ∃ (σ : Measure S) (ρ : X → ℝ) (B : ℝ≥0), IsProbabilityMeasure σ ∧
      σ.map Subtype.val=ν ∧ Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ᵐ x ∂μ, |ρ x| ≤ B) ∧ σ.map Subtype.val=μ.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  let σ : Measure S := ν.comap Subtype.val
  have hprob : IsProbabilityMeasure σ :=
    (MeasurableEmbedding.subtype_coe hS).isProbabilityMeasure_comap (by
      simpa only [Subtype.range_coe] using hs)
  have hmap : σ.map Subtype.val=ν := by
    rw [show σ=ν.comap Subtype.val from rfl,map_comap_subtype_coe hS]
    exact Measure.restrict_eq_self_of_ae_mem hs
  obtain ⟨ρ,B,hρ,hρ0,hρB,heq⟩ := dominated_probability_density μ ν hC hν
  exact ⟨σ,ρ,B,hprob,hmap,hρ,hρ0,hρB,hmap.trans heq⟩

end RegularPointCoordinates

end

end OAI
