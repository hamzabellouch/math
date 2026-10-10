import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteHFBound2
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
variable {V α β : Type*} [MeasurableSpace V]

lemma sourceAngularMomentND_bounded_factor (μ : Measure V) [IsFiniteMeasure μ]
    {U : ℝ × V → ℂ} (hU : Measurable U) {C B : ℝ}
    (hb : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖≤C) (ψ : V → ℂ)
    (hψ : ∀ᵐ w ∂μ, ‖ψ w‖≤B) (r : ℝ) :
    sourceAngularMomentND μ (fun p => ψ p.2*U p) r≤B^2*sourceAngularMomentND μ U r := by
  rw [sourceAngularMomentND,sourceAngularMomentND,← integral_const_mul]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    ((angular_square_integrableND μ (hU.comp (measurable_const.prodMk measurable_id)) (hb r)).const_mul _)
  filter_upwards [hψ] with w hw
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw 2) (sq_nonneg _)

theorem sourceAngularHND_bounded_factors (d : ℕ) (μ : Measure V) [IsFiniteMeasure μ]
    (a v : ℝ) {U W : ℝ × V → ℂ} (hU : Measurable U) (hW : Measurable W)
    {C E B₁ B₂ : ℝ}
    (hbU : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖≤C)
    (hbW : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖≤E)
    (ψ φ : V → ℂ) (hψ : ∀ᵐ w ∂μ, ‖ψ w‖≤B₁) (hφ : ∀ᵐ w ∂μ, ‖φ w‖≤B₂)
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0≤Ψ r) :
    sourceAngularHND d μ a v Ψ (fun p => ψ p.2*U p) (fun p => φ p.2*W p)≤
      B₁^2*B₂^2*sourceAngularHND d μ a v Ψ U W := by
  have hi := graph_weighted_moments_integrableND μ hU hW hbU hbW hΨ
  have hm : (∫ r, Ψ (r/(2:ℝ)^v)*
      sourceAngularMomentND μ (fun p => ψ p.2*U p) r*
      sourceAngularMomentND μ (fun p => φ p.2*W p) r) ≤
      ∫ r, (B₁^2*B₂^2)*(Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun r =>
      mul_nonneg (mul_nonneg (hΨpos _) (sourceAngularMomentND_nonneg _ _ _))
        (sourceAngularMomentND_nonneg _ _ _))) (hi.const_mul _)
    filter_upwards with r
    have h₁ := sourceAngularMomentND_bounded_factor μ hU hbU ψ hψ r
    have h₂ := sourceAngularMomentND_bounded_factor μ hW hbW φ hφ r
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul h₁ h₂ (sourceAngularMomentND_nonneg _ _ _)
        (mul_nonneg (sq_nonneg _) (sourceAngularMomentND_nonneg _ _ _))) (hΨpos (r/(2:ℝ)^v))
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  rw [integral_const_mul] at hm
  dsimp [sourceAngularHND]
  have hh := mul_le_mul_of_nonneg_left hm
    (show 0≤(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹ by positivity)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

theorem graphChildMaxND_bounded_factors (d : ℕ) (μ : Measure V) [IsFiniteMeasure μ]
    (p v : ℝ) (A : Finset α) (B : Finset β) (hAB : (A.product B).Nonempty)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C : α → ℝ) (E : β → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {B₁ B₂ : ℝ}
    (ψ : α → V → ℂ) (φ : β → V → ℂ)
    (hψ : ∀ i∈A, ∀ᵐ w ∂μ, ‖ψ i w‖≤B₁) (hφ : ∀ j∈B, ∀ᵐ w ∂μ, ‖φ j w‖≤B₂)
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0≤Ψ r) :
    graphChildMaxND d μ p v Ψ A B hAB (fun i q => ψ i q.2*U i q) (fun j q => φ j q.2*W j q)≤
      B₁^2*B₂^2*graphChildMaxND d μ p v Ψ A B hAB U W := by
  apply Finset.sup'_le
  intro q hq
  obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
  apply (sourceAngularHND_bounded_factors d μ p v (hU q.1 hq₁) (hW q.2 hq₂)
    (hbU q.1 hq₁) (hbW q.2 hq₂) (ψ q.1) (φ q.2)
    (hψ q.1 hq₁) (hφ q.2 hq₂) hΨ hΨpos).trans
  exact mul_le_mul_of_nonneg_left (Finset.le_sup'
    (fun q => sourceAngularHND d μ p v Ψ (U q.1) (W q.2)) hq) (by positivity)

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
