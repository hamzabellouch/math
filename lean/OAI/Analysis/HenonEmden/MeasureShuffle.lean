import OAI.Analysis.HenonEmden.Tonelli

namespace OAI

universe uA uB uC uD

section MeasureShuffle

open MeasureTheory
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

lemma lintegral_prod_triple_swap (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] {F : (A × B) × C → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(μ.prod ν).prod ρ) =
      ∫⁻ z : (A × C) × B, F ((z.1.1,z.2),z.1.2) ∂(μ.prod ρ).prod ν := by
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, F ((a,b),c) ∂ρ ∂ν ∂μ := by
      rw [lintegral_prod F hF.aemeasurable]
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, F ((a,b),c) ∂ν ∂ρ ∂μ := by
      apply lintegral_congr; intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      rw [lintegral_prod (fun z : (A × C) × B => F ((z.1.1,z.2),z.1.2)) (by fun_prop)]
      exact (lintegral_prod (fun z : A × C => ∫⁻ b, F ((z.1,b),z.2) ∂ν) (by fun_prop)).symm

lemma lintegral_prod_prod_shuffle (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ]
    {F : (A × B) × (C × D) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(μ.prod ν).prod (ρ.prod σ)) =
      ∫⁻ z : (A × C) × (B × D), F ((z.1.1,z.2.1),(z.1.2,z.2.2))
        ∂(μ.prod ρ).prod (ν.prod σ) := by
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, F ((a,b),(c,d)) ∂σ ∂ρ ∂ν ∂μ := by
      rw [lintegral_prod _ hF.aemeasurable,
        lintegral_prod (fun z : A × B => ∫⁻ y : C × D, F (z,y) ∂ρ.prod σ) (by fun_prop)]
      apply lintegral_congr; intro a
      apply lintegral_congr; intro b
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, ∫⁻ d, F ((a,b),(c,d)) ∂σ ∂ν ∂ρ ∂μ := by
      apply lintegral_congr; intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      rw [lintegral_prod (fun z : (A × C) × (B × D) => F ((z.1.1,z.2.1),(z.1.2,z.2.2))) (by fun_prop),
        lintegral_prod (fun z : A × C => ∫⁻ y : B × D, F ((z.1,y.1),(z.2,y.2)) ∂ν.prod σ) (by fun_prop)]
      apply lintegral_congr; intro a
      apply lintegral_congr; intro c
      exact (lintegral_prod (fun z : B × D => F ((a,z.1),(c,z.2))) (by fun_prop)).symm

end HenonLaneEmden.LayerTonelli
end MeasureShuffle

end OAI
