import OAI.MeasureTheory.Falconer.Estimates.PrunedVariation

namespace OAI

/-! # The mask need only be restored inside the coarse filter -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem filtered_masked_variation_on_le (f : X → ℝ) (hf : Measurable f)
    (π : Measure X) (w m : X → ℝ≥0∞) [IsFiniteMeasure (π.withDensity w)]
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1)
    (Γ B : Set X) (hΓ : MeasurableSet Γ) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂π, w x ≤ C)
    (hout : ∀ᵐ x ∂π, x ∈ Γ → x ∉ B → m x = 1) :
    ∃ τ : FiniteMeasure ℝ,
      (τ : Measure ℝ) = ((π.restrict Γ).withDensity (fun x => w x*m x)).map f ∧
      PlanarFalconer.variationDistance
        ⟨filteredPushforward f (π.withDensity w) Γ,inferInstance⟩ τ ≤ C*π B := by
  have hfinite : IsFiniteMeasure ((π.restrict Γ).withDensity w) := by
    rw [← restrict_withDensity hΓ w]
    infer_instance
  let := hfinite
  have hout' : ∀ᵐ x ∂π.restrict Γ, x ∉ B → m x = 1 := by
    filter_upwards [ae_restrict_of_ae hout,ae_restrict_mem hΓ] with x hx hΓx
    exact hx hΓx
  obtain ⟨σ,ρ,hσ,_hρ,hσeq,_hρeq,hvar⟩ := PlanarFalconer.masked_totalVariation_bound
    (π.restrict Γ) f hf w m hw hm hm1 B C (ae_restrict_of_ae hbound) hout'
  refine ⟨⟨σ,hσ⟩,hσeq,?_⟩
  have heq : filteredPushforward f (π.withDensity w) Γ =
      ((π.restrict Γ).withDensity w).map f := by
    unfold filteredPushforward
    rw [restrict_withDensity hΓ w]
  change ((filteredPushforward f (π.withDensity w) Γ).toSignedMeasure -
    σ.toSignedMeasure).totalVariation univ ≤ C*π B
  rw [Measure.toSignedMeasure_congr heq]
  exact hvar.trans (mul_le_mul' le_rfl (Measure.restrict_apply_le Γ B))

end Falconer

end OAI
