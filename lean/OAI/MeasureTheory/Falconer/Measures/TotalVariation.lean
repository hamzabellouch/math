import OAI.MeasureTheory.Falconer.Estimates.MaskLoss
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem totalVariation_sub_of_add {α : Type*} [MeasurableSpace α]
    (τ σ ρ : Measure α) [IsFiniteMeasure τ] [IsFiniteMeasure σ] [IsFiniteMeasure ρ]
    (h : τ = σ+ρ) : (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation = ρ := by
  have heq : τ.toSignedMeasure = σ.toSignedMeasure+ρ.toSignedMeasure := by
    calc
      τ.toSignedMeasure = (σ+ρ).toSignedMeasure := Measure.toSignedMeasure_congr h
      _ = σ.toSignedMeasure+ρ.toSignedMeasure := Measure.toSignedMeasure_add σ ρ
  rw [heq, add_sub_cancel_left, SignedMeasure.totalVariation_eq_variation,
    Measure.variation_toSignedMeasure]

theorem finite_summands {α : Type*} [MeasurableSpace α]
    (τ σ ρ : Measure α) [IsFiniteMeasure τ] (h : τ = σ+ρ) :
    IsFiniteMeasure σ ∧ IsFiniteMeasure ρ := by
  have hσ : σ ≤ τ := by
    rw [h]
    apply Measure.le_iff.mpr
    intro s _
    simp only [Measure.add_apply]
    exact le_add_right le_rfl
  have hρ : ρ ≤ τ := by
    rw [h]
    apply Measure.le_iff.mpr
    intro s _
    simp only [Measure.add_apply]
    exact le_add_left le_rfl
  exact ⟨isFiniteMeasure_of_le τ hσ,isFiniteMeasure_of_le τ hρ⟩

theorem masked_totalVariation_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1)
    [IsFiniteMeasure (μ.withDensity w)] (bad : Set α) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, w x ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ bad → m x = 1) :
    ∃ (σ ρ : Measure β) (_hσ : IsFiniteMeasure σ) (_hρ : IsFiniteMeasure ρ),
      σ = (μ.withDensity (fun x => w x*m x)).map f ∧
      ρ = (μ.withDensity (fun x => w x*(1-m x))).map f ∧
      (((μ.withDensity w).map f).toSignedMeasure-σ.toSignedMeasure).totalVariation univ
        ≤ C*μ bad := by
  let τ := (μ.withDensity w).map f
  let σ := (μ.withDensity (fun x => w x*m x)).map f
  let ρ := (μ.withDensity (fun x => w x*(1-m x))).map f
  have hdec : τ = σ+ρ := masked_pushforward_decomposition μ f hf w m hw hm hm1
  obtain ⟨hσ,hρ⟩ := finite_summands τ σ ρ hdec
  let := hσ
  let := hρ
  refine ⟨σ,ρ,hσ,hρ,rfl,rfl,?_⟩
  rw [totalVariation_sub_of_add τ σ ρ hdec]
  exact removed_pushforward_mass_le μ f hf w m bad C hbound hout

end PlanarFalconer

end OAI
