import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularHFSmul2
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteCutoffEstimate2
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteHFBound

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

theorem graphFiniteHFND_bound (d : ℕ) (a p v lam₁ lam₂ : ℝ)
    (μ : Measure V) [IsFiniteMeasure μ]
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
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0 ≤ Ψ r)
    {ψ : V → ℂ} (hmψ : Measurable ψ) (hψ : ∀ᵐ w ∂μ, ‖ψ w‖ ≤ 1)
    (hi : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p : ℝ × (V × V) => (Ψ (p.1/(2:ℝ)^v):ℂ)*(η k p.2:ℂ)*
        (((ψ p.2.1*U a.1 (p.1,p.2.1))*W a.2 (p.1,p.2.2))*
          conj ((ψ p.2.2*U b.1 (p.1,p.2.2))*W b.2 (p.1,p.2.1)))) (volume.prod (μ.prod μ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, ¬G k a b →
      ‖∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*(η k p.2:ℂ)*
        (((ψ p.2.1*U a.1 (p.1,p.2.1))*W a.2 (p.1,p.2.2))*
          conj ((ψ p.2.2*U b.1 (p.1,p.2.2))*W b.2 (p.1,p.2.1))) ∂volume.prod (μ.prod μ)‖ ≤ ε) :
    sourceAngularHFND d μ a v Ψ ψ (fun z => lam₁ • ∑ i ∈ A, U i z)
      (fun z => lam₂ • ∑ j ∈ B, W j z) ≤
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*
        (∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ p v Ψ (U i) (W j)) +
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
        ((K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε) := by
  have h := graphFiniteCutoffEstimateND μ A B K G η hpart U W hU hW C E hbU hbW
    hD hrow hcol hΨ (fun r => hΨpos (r/(2:ℝ)^v)) hmψ hψ hi hε hne
  have he : (2:ℝ)^((d:ℝ)*(p-a))*(∑ i ∈ A, ∑ j ∈ B,
      sourceAngularHND d μ p v Ψ (U i) (W j)) =
      ∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ a v Ψ (U i) (W j) := by
    simp_rw [Finset.mul_sum,← sourceAngularHND_depth d μ a p v Ψ]
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ lam₁^2*lam₂^2*((2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹) by positivity)
  rw [sourceAngularHFND_smul]
  have hr : lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*
      (∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ p v Ψ (U i) (W j)) =
      lam₁^2*lam₂^2*D*(∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ a v Ψ (U i) (W j)) := by
    rw [← he]
    ring
  rw [hr]
  simp only [sourceAngularHND,sourceAngularHFND,← Finset.mul_sum] at *
  nlinarith only [hm]

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
variable {V α β : Type*} [MeasurableSpace V]

noncomputable def graphChildMaxND (d : ℕ) (μ : Measure V) (p v : ℝ)
    (Ψ : ℝ → ℝ) (A : Finset α) (B : Finset β) (hAB : (A.product B).Nonempty)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ) : ℝ :=
  (A.product B).sup' hAB (fun q => sourceAngularHND d μ p v Ψ (U q.1) (W q.2))

lemma graphChildMaxND_nonneg (d : ℕ) (μ : Measure V) (p v : ℝ)
    (Ψ : ℝ → ℝ) (hΨ : ∀ r, 0 ≤ Ψ r)
    (A : Finset α) (B : Finset β) (hAB : (A.product B).Nonempty)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ) :
    0 ≤ graphChildMaxND d μ p v Ψ A B hAB U W := by
  obtain ⟨q,hq⟩ := hAB
  exact (sourceAngularHND_nonneg d μ p v hΨ (U q.1) (W q.2)).trans
    (Finset.le_sup' (fun q => sourceAngularHND d μ p v Ψ (U q.1) (W q.2)) hq)

lemma graphChild_sum_le_maxND (d : ℕ) (μ : Measure V) (p v : ℝ)
    (Ψ : ℝ → ℝ) (A : Finset α) (B : Finset β) (hAB : (A.product B).Nonempty)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ) :
    (∑ i ∈ A, ∑ j ∈ B, sourceAngularHND d μ p v Ψ (U i) (W j)) ≤
      ((A.card:ℝ)*B.card)*graphChildMaxND d μ p v Ψ A B hAB U W := by
  rw [← Finset.sum_product (f := fun q : α × β => sourceAngularHND d μ p v Ψ (U q.1) (W q.2))]
  calc
    _ ≤ ∑ _q ∈ A.product B, graphChildMaxND d μ p v Ψ A B hAB U W :=
      Finset.sum_le_sum (fun q hq => Finset.le_sup'
        (fun q => sourceAngularHND d μ p v Ψ (U q.1) (W q.2)) hq)
    _ = _ := by simp [Finset.card_product,mul_assoc]

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

lemma graph_profile_prefactorND {N : ℕ} (hN : 0 < N) (d a p : ℝ) :
    (2:ℝ)^(d*(p-a)) = ((2:ℝ)^N)^(d*(p-a)/(N:ℝ)) := by
  rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  have hn : (N:ℝ) ≠ 0 := by positivity
  field_simp

lemma graph_profile_cancellationND {N : ℕ} (hN : 0 < N) (d a p Δ₁ Δ₂ loss : ℝ) :
    let R : ℝ := (2:ℝ)^N
    let I₁ := Δ₁+(d/2)*(p-a)/(N:ℝ)
    let I₂ := Δ₂+(d/2)*(p-a)/(N:ℝ)
    (R^(-I₁))^2*(R^(-I₂))^2*R^(I₁+I₂+loss)*(2:ℝ)^(d*(p-a)) =
      R^(-(Δ₁+Δ₂)+loss) := by
  dsimp only
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [graph_profile_prefactorND hN]
  simp only [← Real.rpow_mul_natCast hR.le,← Real.rpow_add hR]
  congr 1
  push_cast
  ring

theorem graph_profile_coefficient_leND {N : ℕ} (hN : 0 < N)
    (d a p Δ₁ Δ₂ loss degree : ℝ) {D L C : ℝ}
    (hD : 0 ≤ D) (hDL : D ≤ C*((2:ℝ)^N)^degree)
    (hL : L ≤ ((2:ℝ)^N)^(Δ₁+Δ₂+d*(p-a)/(N:ℝ)+loss)) :
    ((((2:ℝ)^N)^(-(Δ₁+(d/2)*(p-a)/(N:ℝ))))^2*
      (((2:ℝ)^N)^(-(Δ₂+(d/2)*(p-a)/(N:ℝ))))^2)*
      (2:ℝ)^(d*(p-a))*D*L ≤
      C*((2:ℝ)^N)^(-(Δ₁+Δ₂)+degree+loss) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by positivity
  let I₁ := Δ₁+(d/2)*(p-a)/(N:ℝ)
  let I₂ := Δ₂+(d/2)*(p-a)/(N:ℝ)
  have he : Δ₁+Δ₂+d*(p-a)/(N:ℝ)=I₁+I₂ := by dsimp [I₁,I₂]; ring
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hL hD) (show 0 ≤ (R^(-I₁))^2*(R^(-I₂))^2*(2:ℝ)^(d*(p-a)) by positivity)
  have h' := mul_le_mul_of_nonneg_right hDL (show 0 ≤ R^(I₁+I₂+loss) by positivity)
  have h'' := mul_le_mul_of_nonneg_left h'
    (show 0 ≤ (R^(-I₁))^2*(R^(-I₂))^2*(2:ℝ)^(d*(p-a)) by positivity)
  change (R^(-I₁))^2*(R^(-I₂))^2*(2:ℝ)^(d*(p-a))*D*L ≤ _
  change L ≤ R^(Δ₁+Δ₂+d*(p-a)/(N:ℝ)+loss) at hL
  rw [he] at hL
  calc
    _ ≤ (R^(-I₁))^2*(R^(-I₂))^2*(2:ℝ)^(d*(p-a))*(D*R^(I₁+I₂+loss)) := by
      simpa only [mul_assoc,he] using h
    _ ≤ (R^(-I₁))^2*(R^(-I₂))^2*(2:ℝ)^(d*(p-a))*((C*R^degree)*R^(I₁+I₂+loss)) := h''
    _ = C*((R^(-I₁))^2*(R^(-I₂))^2*R^(I₁+I₂+loss)*(2:ℝ)^(d*(p-a)))*R^degree := by ring
    _ = C*R^(-(Δ₁+Δ₂)+loss)*R^degree := by rw [graph_profile_cancellationND hN]
    _ = _ := by rw [mul_assoc,← Real.rpow_add hR]; congr 2; ring

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

theorem graphFiniteHND_to_child_max (d : ℕ) (a p v lam₁ lam₂ : ℝ) {N : ℕ} (hN : 0<N)
    (Δ₁ Δ₂ degree loss C₀ : ℝ)
    (hlam₁ : lam₁=((2:ℝ)^N)^(-(Δ₁+(d:ℝ)/2*(p-a)/(N:ℝ))))
    (hlam₂ : lam₂=((2:ℝ)^N)^(-(Δ₂+(d:ℝ)/2*(p-a)/(N:ℝ))))
    (μ : Measure V) [IsFiniteMeasure μ]
    (A : Finset α) (B : Finset β) (K : Finset κ) (hAB : (A.product B).Nonempty)
    (hlabels : ((A.card:ℝ)*B.card) ≤ ((2:ℝ)^N)^(Δ₁+Δ₂+(d:ℝ)*(p-a)/(N:ℝ)+loss))
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (η : κ → V × V → ℝ)
    (hpart : ∀ᵐ z ∂μ.prod μ, (∀ k ∈ K, 0 ≤ η k z) ∧ ∑ k ∈ K, η k z=1)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i ∈ A, Measurable (U i)) (hW : ∀ j ∈ B, Measurable (W j))
    (C : α → ℝ) (E : β → ℝ)
    (hbU : ∀ i ∈ A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖ ≤ C i)
    (hbW : ∀ j ∈ B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖ ≤ E j) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : D ≤ C₀*((2:ℝ)^N)^degree)
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
      C₀*((2:ℝ)^N)^(-(Δ₁+Δ₂)+degree+loss)*
        graphChildMaxND d μ p v Ψ A B hAB U W +
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
        ((K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε) := by
  have h := graphFiniteHND_bound d a p v lam₁ lam₂ μ A B K G η hpart U W hU hW C E hbU hbW
    D hrow hcol hΨ hΨpos hi hε hne
  have hs := graphChild_sum_le_maxND d μ p v Ψ A B hAB U W
  have hmax := graphChildMaxND_nonneg d μ p v Ψ hΨpos A B hAB U W
  have hc : lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*((A.card:ℝ)*B.card) ≤
      C₀*((2:ℝ)^N)^(-(Δ₁+Δ₂)+degree+loss) := by
    rw [hlam₁,hlam₂]
    exact graph_profile_coefficient_leND hN d a p Δ₁ Δ₂ loss degree hD hdegree hlabels
  apply h.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ (lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D)*
        (((A.card:ℝ)*B.card)*graphChildMaxND d μ p v Ψ A B hAB U W) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*((A.card:ℝ)*B.card))*
        graphChildMaxND d μ p v Ψ A B hAB U W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hmax

theorem graphFiniteHFND_to_child_max (d : ℕ) (a p v lam₁ lam₂ : ℝ) {N : ℕ} (hN : 0<N)
    (Δ₁ Δ₂ degree loss C₀ : ℝ)
    (hlam₁ : lam₁=((2:ℝ)^N)^(-(Δ₁+(d:ℝ)/2*(p-a)/(N:ℝ))))
    (hlam₂ : lam₂=((2:ℝ)^N)^(-(Δ₂+(d:ℝ)/2*(p-a)/(N:ℝ))))
    (μ : Measure V) [IsFiniteMeasure μ]
    (A : Finset α) (B : Finset β) (K : Finset κ) (hAB : (A.product B).Nonempty)
    (hlabels : ((A.card:ℝ)*B.card) ≤ ((2:ℝ)^N)^(Δ₁+Δ₂+(d:ℝ)*(p-a)/(N:ℝ)+loss))
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (η : κ → V × V → ℝ)
    (hpart : ∀ᵐ z ∂μ.prod μ, (∀ k ∈ K, 0 ≤ η k z) ∧ ∑ k ∈ K, η k z=1)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i ∈ A, Measurable (U i)) (hW : ∀ j ∈ B, Measurable (W j))
    (C : α → ℝ) (E : β → ℝ)
    (hbU : ∀ i ∈ A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖ ≤ C i)
    (hbW : ∀ j ∈ B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖ ≤ E j) {D : ℝ} (hD : 0 ≤ D)
    (hdegree : D ≤ C₀*((2:ℝ)^N)^degree)
    (hrow : ∀ k ∈ K, ∀ a ∈ A.product B, (((A.product B).filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ A.product B, (((A.product B).filter (fun a => G k a b)).card : ℝ) ≤ D)
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0 ≤ Ψ r)
    {ψ : V → ℂ} (hmψ : Measurable ψ) (hψ : ∀ᵐ w ∂μ, ‖ψ w‖ ≤ 1)
    (hi : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p : ℝ × (V × V) => (Ψ (p.1/(2:ℝ)^v):ℂ)*(η k p.2:ℂ)*
        (((ψ p.2.1*U a.1 (p.1,p.2.1))*W a.2 (p.1,p.2.2))*
          conj ((ψ p.2.2*U b.1 (p.1,p.2.2))*W b.2 (p.1,p.2.1)))) (volume.prod (μ.prod μ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, ¬G k a b →
      ‖∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*(η k p.2:ℂ)*
        (((ψ p.2.1*U a.1 (p.1,p.2.1))*W a.2 (p.1,p.2.2))*
          conj ((ψ p.2.2*U b.1 (p.1,p.2.2))*W b.2 (p.1,p.2.1))) ∂volume.prod (μ.prod μ)‖ ≤ ε) :
    sourceAngularHFND d μ a v Ψ ψ (fun z => lam₁ • ∑ i ∈ A, U i z)
      (fun z => lam₂ • ∑ j ∈ B, W j z) ≤
      C₀*((2:ℝ)^N)^(-(Δ₁+Δ₂)+degree+loss)*
        graphChildMaxND d μ p v Ψ A B hAB U W +
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
        ((K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε) := by
  have h := graphFiniteHFND_bound d a p v lam₁ lam₂ μ A B K G η hpart U W hU hW C E hbU hbW
    hD hrow hcol hΨ hΨpos hmψ hψ hi hε hne
  have hs := graphChild_sum_le_maxND d μ p v Ψ A B hAB U W
  have hmax := graphChildMaxND_nonneg d μ p v Ψ hΨpos A B hAB U W
  have hc : lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*((A.card:ℝ)*B.card) ≤
      C₀*((2:ℝ)^N)^(-(Δ₁+Δ₂)+degree+loss) := by
    rw [hlam₁,hlam₂]
    exact graph_profile_coefficient_leND hN d a p Δ₁ Δ₂ loss degree hD hdegree hlabels
  apply h.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ (lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D)*
        (((A.card:ℝ)*B.card)*graphChildMaxND d μ p v Ψ A B hAB U W) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(p-a))*D*((A.card:ℝ)*B.card))*
        graphChildMaxND d μ p v Ψ A B hAB U W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hmax

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
