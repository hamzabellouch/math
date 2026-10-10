import OAI.MeasureTheory.Falconer.Estimates.FilteredLimit
import OAI.MeasureTheory.Falconer.Shells.Shells
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! # Exact variation cost of deleting original pairs

The full filtered measure is monotone in the coarse filter. Its pruned
approximation differs by precisely the weighted mass of the removed pairs.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem filteredPushforward_prune_variation (f : X → ℝ) (hf : Measurable f)
    (ρ : Measure X) [IsFiniteMeasure ρ] (Γ B : Set X) (hB : MeasurableSet B) :
    PlanarFalconer.variationDistance
      ⟨filteredPushforward f ρ Γ,inferInstance⟩
      ⟨filteredPushforward f ρ (Γ \ B),inferInstance⟩ = ρ (Γ ∩ B) := by
  have hdec : filteredPushforward f ρ Γ =
      filteredPushforward f ρ (Γ \ B) + filteredPushforward f ρ (Γ ∩ B) := by
    unfold filteredPushforward
    rw [← Measure.map_add _ _ hf,add_comm,Measure.restrict_inter_add_sdiff Γ hB]
  change ((filteredPushforward f ρ Γ).toSignedMeasure -
    (filteredPushforward f ρ (Γ \ B)).toSignedMeasure).totalVariation univ = _
  rw [PlanarFalconer.totalVariation_sub_of_add _ _ _ hdec,
    filteredPushforward_mass f hf]

theorem finite_withDensity_of_bounded (π : Measure X) [IsFiniteMeasure π]
    (w : X → ℝ≥0∞) {C : ℝ≥0∞} (hC : C < ∞) (hbound : ∀ᵐ x ∂π, w x ≤ C) :
    IsFiniteMeasure (π.withDensity w) := by
  constructor
  rw [withDensity_apply w MeasurableSet.univ,Measure.restrict_univ]
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hC (measure_lt_top π univ)

theorem weighted_prune_variation_le (f : X → ℝ) (hf : Measurable f)
    (π : Measure X) [IsFiniteMeasure π] (w : X → ℝ≥0∞)
    {C : ℝ≥0∞} (hC : C < ∞) (hbound : ∀ᵐ x ∂π, w x ≤ C)
    (Γ B : Set X) (hΓ : MeasurableSet Γ) (hB : MeasurableSet B) :
    letI := finite_withDensity_of_bounded π w hC hbound
    PlanarFalconer.variationDistance
      ⟨filteredPushforward f (π.withDensity w) Γ,inferInstance⟩
      ⟨filteredPushforward f (π.withDensity w) (Γ \ B),inferInstance⟩ ≤ C * π B := by
  let := finite_withDensity_of_bounded π w hC hbound
  rw [filteredPushforward_prune_variation f hf _ Γ B hB,
    withDensity_apply w (hΓ.inter hB)]
  calc
    _ ≤ ∫⁻ _ in Γ ∩ B, C ∂π := lintegral_mono_ae (ae_restrict_of_ae hbound)
    _ = C * π (Γ ∩ B) := by rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ C * π B := mul_le_mul' le_rfl (measure_mono inter_subset_right)

theorem withDensity_positive_of_lower (π : Measure X) (w : X → ℝ≥0∞)
    {c : ℝ≥0∞} (hc : 0 < c) (hbound : ∀ᵐ x ∂π, c ≤ w x)
    (S : Set X) (hS : MeasurableSet S) (hpos : 0 < π S) :
    0 < π.withDensity w S := by
  rw [withDensity_apply w hS]
  have hlow : c * π S ≤ ∫⁻ x in S, w x ∂π := by
    rw [← Measure.restrict_apply_univ (μ := π) (s := S),← lintegral_const]
    exact lintegral_mono_ae (ae_restrict_of_ae hbound)
  exact (ENNReal.mul_pos hc.ne' hpos.ne').trans_le hlow

/-- Smooth masks incur the same original-pair deletion cost as sharp pruning.
The exceptional set is measured before the coarse filter is imposed. -/
theorem filtered_masked_variation_le (f : X → ℝ) (hf : Measurable f)
    (π : Measure X) (w m : X → ℝ≥0∞) [IsFiniteMeasure (π.withDensity w)]
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1)
    (Γ B : Set X) (hΓ : MeasurableSet Γ) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂π, w x ≤ C) (hout : ∀ᵐ x ∂π, x ∉ B → m x = 1) :
    ∃ τ : FiniteMeasure ℝ,
      (τ : Measure ℝ) = ((π.restrict Γ).withDensity (fun x => w x*m x)).map f ∧
      PlanarFalconer.variationDistance
        ⟨filteredPushforward f (π.withDensity w) Γ,inferInstance⟩ τ ≤ C*π B := by
  have hfinite : IsFiniteMeasure ((π.restrict Γ).withDensity w) := by
    rw [← restrict_withDensity hΓ w]
    infer_instance
  let := hfinite
  obtain ⟨σ,ρ,hσ,_hρ,hσeq,_hρeq,hvar⟩ := PlanarFalconer.masked_totalVariation_bound
    (π.restrict Γ) f hf w m hw hm hm1 B C
    (ae_restrict_of_ae hbound) (ae_restrict_of_ae hout)
  refine ⟨⟨σ,hσ⟩,hσeq,?_⟩
  change ((filteredPushforward f (π.withDensity w) Γ).toSignedMeasure -
    σ.toSignedMeasure).totalVariation univ ≤ C*π B
  have heq : filteredPushforward f (π.withDensity w) Γ =
      ((π.restrict Γ).withDensity w).map f := by
    unfold filteredPushforward
    rw [restrict_withDensity hΓ w]
  rw [Measure.toSignedMeasure_congr heq]
  exact hvar.trans (mul_le_mul' le_rfl (Measure.restrict_apply_le Γ B))

end Falconer

end OAI
