import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteCrossedEstimate
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteCutoffEstimate
import OAI.MeasureTheory.FalconerCompletion.Recursion.AngularMomentLe2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ComplexConjugate
variable {V α β κ : Type*} [MeasurableSpace V]

theorem graphFiniteCutoffEstimateND (μ : Measure V) [IsFiniteMeasure μ]
    (A : Finset α) (B : Finset β) (K : Finset κ)
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (η : κ → V × V → ℝ)
    (hpart : ∀ᵐ z ∂μ.prod μ, (∀ k ∈ K, 0 ≤ η k z) ∧ ∑ k ∈ K, η k z=1)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i ∈ A, Measurable (U i)) (hW : ∀ j ∈ B, Measurable (W j))
    (C : α → ℝ) (E : β → ℝ)
    (hbU : ∀ i ∈ A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖ ≤ C i)
    (hbW : ∀ j ∈ B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖ ≤ E j) {D : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ k ∈ K, ∀ a ∈ A.product B, (((A.product B).filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ A.product B, (((A.product B).filter (fun a => G k a b)).card : ℝ) ≤ D)
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) (hΨpos : ∀ r, 0 ≤ Ψ r)
    {ψ : V → ℂ} (hmψ : Measurable ψ) (hψ : ∀ᵐ w ∂μ, ‖ψ w‖ ≤ 1)
    (hi : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*(η k p.2:ℂ)*
        (((ψ p.2.1*U a.1 (p.1,p.2.1))*W a.2 (p.1,p.2.2))*
          conj ((ψ p.2.2*U b.1 (p.1,p.2.2))*W b.2 (p.1,p.2.1)))) (volume.prod (μ.prod μ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, ¬G k a b →
      ‖∫ p : ℝ × (V × V), (Ψ p.1:ℂ)*(η k p.2:ℂ)*
        (((ψ p.2.1*U a.1 (p.1,p.2.1))*W a.2 (p.1,p.2.2))*
          conj ((ψ p.2.2*U b.1 (p.1,p.2.2))*W b.2 (p.1,p.2.1))) ∂volume.prod (μ.prod μ)‖ ≤ ε) :
    (∫ r, Ψ r*‖∫ w, ψ w*(∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2) ≤
      D*∑ i ∈ A, ∑ j ∈ B, (∫ r, Ψ r*sourceAngularMomentND μ (U i) r*
        sourceAngularMomentND μ (W j) r) + (K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε := by
  have hUb (i) (hi : i ∈ A) (r : ℝ) : ∀ᵐ w ∂μ, ‖ψ w*U i (r,w)‖ ≤ C i := by
    filter_upwards [hψ,hbU i hi r] with w hw hu
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans (by simpa using hu)
  have h := graphFiniteCrossedEstimateND μ A B K G η hpart (fun i z => ψ z.2*U i z)
    W (fun i hi => (hmψ.comp measurable_snd).mul (hU i hi)) hW C E hUb hbW D
    hrow hcol hΨ hΨpos hi hε hne
  simp_rw [← Finset.mul_sum] at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hD
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun r => mul_nonneg
    (mul_nonneg (hΨpos r) (sourceAngularMomentND_nonneg μ _ r)) (sourceAngularMomentND_nonneg μ _ r)))
    (graph_weighted_moments_integrableND μ (hU i hi) (hW j hj) (hbU i hi) (hbW j hj) hΨ)
  filter_upwards with r
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (sourceAngularMomentND_cutoff_le μ (hU i hi) (hbU i hi) ψ hψ r) (hΨpos r))
      (sourceAngularMomentND_nonneg μ _ r)

end Attempt4Near
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ComplexConjugate
variable {V α β κ : Type*} [MeasurableSpace V]

theorem graphFiniteHND_bound (d : ℕ) (a p v lam₁ lam₂ : ℝ)
    (μ : Measure V) [IsFiniteMeasure μ]
    (A : Finset α) (B : Finset β) (K : Finset κ)
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (η : κ → V × V → ℝ)
    (hpart : ∀ᵐ z ∂μ.prod μ, (∀ k ∈ K, 0 ≤ η k z) ∧ ∑ k ∈ K, η k z=1)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i ∈ A, Measurable (U i)) (hW : ∀ j ∈ B, Measurable (W j))
    (C : α → ℝ) (E : β → ℝ)
    (hbU : ∀ i ∈ A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖ ≤ C i)
    (hbW : ∀ j ∈ B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖ ≤ E j) (D : ℝ)
    (hrow : ∀ k ∈ K, ∀ a ∈ A.product B, (((A.product B).filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ A.product B, (((A.product B).filter (fun a => G k a b)).card : ℝ) ≤ D)
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0 ≤ Ψ r)
    (hi : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p : ℝ × (V × V) => (Ψ (p.1/(2:ℝ)^v):ℂ)*(η k p.2:ℂ)*
        ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*
          conj (U b.1 (p.1,p.2.1)*W b.2 (p.1,p.2.2)))) (volume.prod (μ.prod μ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, ¬G k a b →
      ‖∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*(η k p.2:ℂ)*
        ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*
          conj (U b.1 (p.1,p.2.1)*W b.2 (p.1,p.2.2))) ∂volume.prod (μ.prod μ)‖ ≤ ε) :
    sourceAngularHND d μ a v Ψ (fun z => lam₁ • ∑ i ∈ A, U i z)
      (fun z => lam₂ • ∑ j ∈ B, W j z) ≤
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*
        (∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ p v Ψ (U i) (W j)) +
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
        ((K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε) := by
  have h := graphFiniteDirectEstimateND μ A B K G η hpart U W hU hW C E hbU hbW
    D hrow hcol hΨ (fun r => hΨpos (r/(2:ℝ)^v)) hi hε hne
  have he : (2:ℝ)^((d:ℝ)*(p-a))*(∑ i ∈ A, ∑ j ∈ B,
      sourceAngularHND d μ p v Ψ (U i) (W j)) =
      ∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ a v Ψ (U i) (W j) := by
    simp_rw [Finset.mul_sum,← sourceAngularHND_depth d μ a p v Ψ]
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ lam₁^2*lam₂^2*((2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹) by positivity)
  rw [sourceAngularHND_smul]
  have hr : lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*
      (∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ p v Ψ (U i) (W j)) =
      lam₁^2*lam₂^2*D*(∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ a v Ψ (U i) (W j)) := by
    rw [← he]
    ring
  rw [hr]
  simp only [sourceAngularHND,← Finset.mul_sum] at *
  nlinarith only [hm]

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
