import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphRetainedDirect

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

theorem graphFiniteCrossedEstimateND (μ : Measure V) [IsFiniteMeasure μ]
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
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) (hΨpos : ∀ r, 0 ≤ Ψ r)
    (hi : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*(η k p.2:ℂ)*
        ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*
          conj (U b.1 (p.1,p.2.2)*W b.2 (p.1,p.2.1)))) (volume.prod (μ.prod μ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, ¬G k a b →
      ‖∫ p : ℝ × (V × V), (Ψ p.1:ℂ)*(η k p.2:ℂ)*
        ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*
          conj (U b.1 (p.1,p.2.2)*W b.2 (p.1,p.2.1))) ∂volume.prod (μ.prod μ)‖ ≤ ε) :
    (∫ r, Ψ r*‖∫ w, (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2) ≤
      D*∑ i ∈ A, ∑ j ∈ B, (∫ r, Ψ r*sourceAngularMomentND μ (U i) r*
        sourceAngularMomentND μ (W j) r) + (K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε := by
  let F := fun (k : κ) (a b : α × β) (p : ℝ × (V × V)) => (Ψ p.1:ℂ)*(η k p.2:ℂ)*
    ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*conj (U b.1 (p.1,p.2.2)*W b.2 (p.1,p.2.1)))
  have hiF : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (F k a b) (volume.prod (μ.prod μ)) := hi
  have hiR : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p => if G k a b then F k a b p else 0) (volume.prod (μ.prod μ)) := by
    intro k hk a ha b hb
    by_cases h : G k a b
    · simpa only [h,ite_true] using hiF k hk a ha b hb
    · simp only [h,ite_false]; exact integrable_zero _ _ _
  have heF : (fun p => ∑ k ∈ K, ∑ a ∈ A.product B, ∑ b ∈ A.product B, F k a b p) =
      fun p => (Ψ p.1:ℂ)*graphRetainedCrossedND A B K (fun _ _ _ => True) η U W p.1 p.2 := by
    funext p
    simp only [F,graphRetainedCrossedND,ite_true,Finset.mul_sum,mul_assoc]
  have heR : (fun p => ∑ k ∈ K, ∑ a ∈ A.product B, ∑ b ∈ A.product B,
        if G k a b then F k a b p else 0) =
      fun p => (Ψ p.1:ℂ)*graphRetainedCrossedND A B K G η U W p.1 p.2 := by
    funext p
    simp only [F,graphRetainedCrossedND,Finset.mul_sum,mul_ite,mul_zero,mul_assoc]
  have hintF := integrable_finsetSum K (fun k hk => integrable_finsetSum (A.product B)
    (fun a ha => integrable_finsetSum (A.product B) (fun b hb => hiF k hk a ha b hb)))
  have hintR := integrable_finsetSum K (fun k hk => integrable_finsetSum (A.product B)
    (fun a ha => integrable_finsetSum (A.product B) (fun b hb => hiR k hk a ha b hb)))
  rw [heF] at hintF
  rw [heR] at hintR
  have hl := graph_integral_localizationND (volume.prod (μ.prod μ)) A B K G F hiF hε hne
  rw [heF,heR,integral_prod _ hintF,integral_prod _ hintR] at hl
  simp_rw [integral_const_mul] at hl
  have he (r : ℝ) := graphExpandedCrossedND_integral μ A B K η U W r
    (hpart.mono (fun _ h => h.2))
  simp_rw [he] at hl
  simp only [← Complex.ofReal_mul] at hl
  rw [integral_complex_ofReal] at hl
  have hb := graphRetainedCrossedND_integral_bound μ A B K G η hpart U W hU hW C E hbU hbW
    D hrow hcol hΨ hΨpos
  have hnon : 0 ≤ ∫ r, Ψ r*‖∫ w, (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2 := integral_nonneg (fun r =>
        mul_nonneg (hΨpos r) (sq_nonneg _))
  have htt : ‖((∫ r, Ψ r*‖∫ w, (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2 : ℝ):ℂ)‖ ≤ ‖(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ)‖ + ‖((∫ r, Ψ r*‖∫ w, (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2 : ℝ):ℂ)-(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ)‖ := by
    calc
      _ = ‖(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ)+(((∫ r, Ψ r*‖∫ w, (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2 : ℝ):ℂ)-(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ))‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon] at htt
  exact htt.trans (add_le_add hb (by simpa only [mul_assoc] using hl))

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
