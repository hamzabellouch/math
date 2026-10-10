import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMoment
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteDirectEstimate

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
noncomputable def graphRetainedDirectND (A : Finset α) (B : Finset β) (K : Finset κ)
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (η : κ → V × V → ℝ) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (r : ℝ) (z : V × V) : ℂ :=
  ∑ k ∈ K, (η k z:ℂ)*(∑ a ∈ A.product B, ∑ b ∈ A.product B,
    if G k a b then (U a.1 (r,z.1)*W a.2 (r,z.2))*
      conj (U b.1 (r,z.1)*W b.2 (r,z.2)) else 0)

lemma graphRetainedDirectND_angular_bound (μ : Measure V) [IsFiniteMeasure μ]
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
    (r : ℝ) :
    ‖∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ‖ ≤
      D*∑ i ∈ A, ∑ j ∈ B, sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r := by
  have hi := graphChildSquareND_integrable μ A B U W hU hW C E hbU hbW r
  have hb := norm_integral_le_of_norm_le (hi.const_mul D)
    (show ∀ᵐ z ∂μ.prod μ, ‖graphRetainedDirectND A B K G η U W r z‖ ≤
      D*graphChildSquareND A B U W r z from by
      filter_upwards [hpart] with z hz
      have hh := graph_partition_product_schurND A B K G
        (fun i => U i (r,z.1)) (fun i => U i (r,z.1))
        (fun j => W j (r,z.2)) (fun j => W j (r,z.2)) (fun k => η k z) hz.1 hz.2 D hrow hcol
      convert hh using 1
      · rfl
      · dsimp [graphChildSquareND]
        ring)
  rw [integral_const_mul,graphChildSquareND_integral μ A B U W hU hW C E hbU hbW] at hb
  exact hb

theorem graphRetainedDirectND_integral_bound (μ : Measure V) [IsFiniteMeasure μ]
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
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) (hΨpos : ∀ r, 0 ≤ Ψ r) :
    ‖∫ r, (Ψ r:ℂ)*∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ‖ ≤
      D*∑ i ∈ A, ∑ j ∈ B, ∫ r, Ψ r*sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r := by
  have hi (i) (hi : i ∈ A) (j) (hj : j ∈ B) :=
    graph_weighted_moments_integrableND μ (hU i hi) (hW j hj) (hbU i hi) (hbW j hj) hΨ
  have hs := (integrable_finsetSum A (fun i hiA => integrable_finsetSum B
    (fun j hjB => hi i hiA j hjB))).const_mul D
  have hh := norm_integral_le_of_norm_le hs
    (show ∀ᵐ r : ℝ, ‖(Ψ r:ℂ)*∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ‖ ≤
      D*∑ i ∈ A, ∑ j ∈ B, Ψ r*sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r from by
      filter_upwards with r
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hΨpos r)]
      have hp := mul_le_mul_of_nonneg_left (graphRetainedDirectND_angular_bound
        μ A B K G η hpart U W hU hW C E hbU hbW D hrow hcol r) (hΨpos r)
      simpa only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using hp)
  rw [integral_const_mul,integral_finsetSum A (fun i hiA => integrable_finsetSum B
    (fun j hjB => hi i hiA j hjB))] at hh
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro i hiA
  exact integral_finsetSum B (fun j hjB => hi i hiA j hjB)
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

lemma graph_four_sumND (A : Finset α) (B : Finset β)
    (U₁ U₂ : α → ℂ) (W₁ W₂ : β → ℂ) :
    (∑ a ∈ A.product B, ∑ b ∈ A.product B,
      (U₁ a.1*W₁ a.2)*conj (U₂ b.1*W₂ b.2)) =
      ((∑ i ∈ A, U₁ i)*(∑ j ∈ B, W₁ j))*conj ((∑ i ∈ A, U₂ i)*(∑ j ∈ B, W₂ j)) := by
  rw [← Finset.sum_mul_sum,← map_sum]
  simp_rw [Finset.product_eq_sprod,Finset.sum_product,← Finset.sum_mul_sum]

omit [MeasurableSpace V] in
lemma graphRetainedDirectND_complete (A : Finset α) (B : Finset β) (K : Finset κ)
    (η : κ → V × V → ℝ) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (r : ℝ) (z : V × V) (hpart : ∑ k ∈ K, η k z=1) :
    graphRetainedDirectND A B K (fun _ _ _ => True) η U W r z =
      ((‖∑ i ∈ A, U i (r,z.1)‖^2*‖∑ j ∈ B, W j (r,z.2)‖^2:ℝ):ℂ) := by
  simp only [graphRetainedDirectND,ite_true]
  rw [← Finset.sum_mul,← Complex.ofReal_sum,hpart,Complex.ofReal_one,one_mul,
    graph_four_sumND A B (fun i => U i (r,z.1)) (fun i => U i (r,z.1))
      (fun j => W j (r,z.2)) (fun j => W j (r,z.2)),
    Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_mul,mul_pow]

omit [MeasurableSpace V] in
lemma graphRetainedCrossedND_complete (A : Finset α) (B : Finset β) (K : Finset κ)
    (η : κ → V × V → ℝ) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (r : ℝ) (z : V × V) (hpart : ∑ k ∈ K, η k z=1) :
    graphRetainedCrossedND A B K (fun _ _ _ => True) η U W r z =
      ((∑ i ∈ A, U i (r,z.1))*conj (∑ j ∈ B, W j (r,z.1)))*
        conj ((∑ i ∈ A, U i (r,z.2))*conj (∑ j ∈ B, W j (r,z.2))) := by
  simp only [graphRetainedCrossedND,ite_true]
  rw [← Finset.sum_mul,← Complex.ofReal_sum,hpart,Complex.ofReal_one,one_mul]
  rw [graph_four_sumND A B (fun i => U i (r,z.1)) (fun i => U i (r,z.2))
      (fun j => W j (r,z.2)) (fun j => W j (r,z.1))]
  simp only [map_mul,starRingEnd_self_apply]
  ring

lemma graphExpandedDirectND_integral (μ : Measure V) [SFinite μ]
    (A : Finset α) (B : Finset β) (K : Finset κ)
    (η : κ → V × V → ℝ) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (r : ℝ) (hpart : ∀ᵐ z ∂μ.prod μ, ∑ k ∈ K, η k z=1) :
    (∫ z, graphRetainedDirectND A B K (fun _ _ _ => True) η U W r z ∂μ.prod μ) =
      ((sourceAngularMomentND μ (fun z => ∑ i ∈ A, U i z) r*
        sourceAngularMomentND μ (fun z => ∑ j ∈ B, W j z) r:ℝ):ℂ) := by
  calc
    _ = ∫ z : V × V, ((‖∑ i ∈ A, U i (r,z.1)‖^2*‖∑ j ∈ B, W j (r,z.2)‖^2:ℝ):ℂ)
        ∂μ.prod μ := integral_congr_ae (by
      filter_upwards [hpart] with z hz
      exact graphRetainedDirectND_complete A B K η U W r z hz)
    _ = _ := by
      rw [integral_complex_ofReal,integral_prod_mul
        (fun w => ‖∑ i ∈ A, U i (r,w)‖^2) (fun w => ‖∑ j ∈ B, W j (r,w)‖^2)]
      rfl

lemma graphExpandedCrossedND_integral (μ : Measure V) [SFinite μ]
    (A : Finset α) (B : Finset β) (K : Finset κ)
    (η : κ → V × V → ℝ) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (r : ℝ) (hpart : ∀ᵐ z ∂μ.prod μ, ∑ k ∈ K, η k z=1) :
    (∫ z, graphRetainedCrossedND A B K (fun _ _ _ => True) η U W r z ∂μ.prod μ) =
      ((‖∫ w, (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)) ∂μ‖^2:ℝ):ℂ) := by
  calc
    _ = ∫ z : V × V, ((∑ i ∈ A, U i (r,z.1))*conj (∑ j ∈ B, W j (r,z.1)))*
        conj ((∑ i ∈ A, U i (r,z.2))*conj (∑ j ∈ B, W j (r,z.2))) ∂μ.prod μ :=
      integral_congr_ae (by
        filter_upwards [hpart] with z hz
        exact graphRetainedCrossedND_complete A B K η U W r z hz)
    _ = _ := by
      rw [integral_prod_mul
        (fun w => (∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)))
        (fun w => conj ((∑ i ∈ A, U i (r,w))*conj (∑ j ∈ B, W j (r,w)))),
        integral_conj,Complex.mul_conj,Complex.normSq_eq_norm_sq]

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
open MeasureTheory
open scoped BigOperators
variable {Z α β κ : Type*} [MeasurableSpace Z]

lemma graph_integral_sum_truncateND (μ : Measure Z) (S : Finset α)
    (G : α → Prop) [DecidablePred G] (F : α → Z → ℂ)
    (hi : ∀ i ∈ S, Integrable (F i) μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ i ∈ S, ¬G i → ‖∫ z, F i z ∂μ‖ ≤ ε) :
    ‖(∫ z, ∑ i ∈ S, F i z ∂μ)-(∫ z, ∑ i ∈ S, if G i then F i z else 0 ∂μ)‖ ≤
      S.card*ε := by
  have hit (i : α) (hiS : i ∈ S) : Integrable (fun z => if G i then F i z else 0) μ := by
    by_cases h : G i
    · simpa only [h,ite_true] using hi i hiS
    · simp only [h,ite_false]; exact integrable_zero _ _ _
  rw [integral_finsetSum S hi,integral_finsetSum S hit]
  have he : (∑ i ∈ S, ∫ z, if G i then F i z else 0 ∂μ) =
      ∑ i ∈ S.filter G, ∫ z, F i z ∂μ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : G i <;> simp [h]
  rw [he]
  exact graph_discarded_sumND S G (fun i => ∫ z, F i z ∂μ) hε hne

lemma graph_integral_localizationND (μ : Measure Z) (A : Finset α) (B : Finset β) (K : Finset κ)
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (F : κ → (α × β) → (α × β) → Z → ℂ)
    (hi : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, Integrable (F k a b) μ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      ¬G k a b → ‖∫ z, F k a b z ∂μ‖ ≤ ε) :
    ‖(∫ z, ∑ k ∈ K, ∑ a ∈ A.product B, ∑ b ∈ A.product B, F k a b z ∂μ)-
      (∫ z, ∑ k ∈ K, ∑ a ∈ A.product B, ∑ b ∈ A.product B,
        if G k a b then F k a b z else 0 ∂μ)‖ ≤
      (K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε := by
  let S := K.product ((A.product B).product (A.product B))
  have h := graph_integral_sum_truncateND μ S
    (fun z => G z.1 z.2.1 z.2.2) (fun z => F z.1 z.2.1 z.2.2)
    (fun z hz => hi z.1 (Finset.mem_product.mp hz).1
      z.2.1 (Finset.mem_product.mp (Finset.mem_product.mp hz).2).1
      z.2.2 (Finset.mem_product.mp (Finset.mem_product.mp hz).2).2) hε
    (fun z hz => hne z.1 (Finset.mem_product.mp hz).1
      z.2.1 (Finset.mem_product.mp (Finset.mem_product.mp hz).2).1
      z.2.2 (Finset.mem_product.mp (Finset.mem_product.mp hz).2).2)
  simpa only [S,Finset.product_eq_sprod,Finset.sum_product,Finset.card_product,
    Nat.cast_mul,pow_two,mul_assoc] using h

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

theorem graphFiniteDirectEstimateND (μ : Measure V) [IsFiniteMeasure μ]
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
          conj (U b.1 (p.1,p.2.1)*W b.2 (p.1,p.2.2)))) (volume.prod (μ.prod μ)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hne : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B, ¬G k a b →
      ‖∫ p : ℝ × (V × V), (Ψ p.1:ℂ)*(η k p.2:ℂ)*
        ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*
          conj (U b.1 (p.1,p.2.1)*W b.2 (p.1,p.2.2))) ∂volume.prod (μ.prod μ)‖ ≤ ε) :
    (∫ r, Ψ r*sourceAngularMomentND μ (fun z => ∑ i ∈ A, U i z) r*
      sourceAngularMomentND μ (fun z => ∑ j ∈ B, W j z) r) ≤
      D*∑ i ∈ A, ∑ j ∈ B, (∫ r, Ψ r*sourceAngularMomentND μ (U i) r*
        sourceAngularMomentND μ (W j) r) + (K.card:ℝ)*((A.card:ℝ)*B.card)^2*ε := by
  let F := fun (k : κ) (a b : α × β) (p : ℝ × (V × V)) => (Ψ p.1:ℂ)*(η k p.2:ℂ)*
    ((U a.1 (p.1,p.2.1)*W a.2 (p.1,p.2.2))*conj (U b.1 (p.1,p.2.1)*W b.2 (p.1,p.2.2)))
  have hiF : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (F k a b) (volume.prod (μ.prod μ)) := hi
  have hiR : ∀ k ∈ K, ∀ a ∈ A.product B, ∀ b ∈ A.product B,
      Integrable (fun p => if G k a b then F k a b p else 0) (volume.prod (μ.prod μ)) := by
    intro k hk a ha b hb
    by_cases h : G k a b
    · simpa only [h,ite_true] using hiF k hk a ha b hb
    · simp only [h,ite_false]; exact integrable_zero _ _ _
  have heF : (fun p => ∑ k ∈ K, ∑ a ∈ A.product B, ∑ b ∈ A.product B, F k a b p) =
      fun p => (Ψ p.1:ℂ)*graphRetainedDirectND A B K (fun _ _ _ => True) η U W p.1 p.2 := by
    funext p
    simp only [F,graphRetainedDirectND,ite_true,Finset.mul_sum,mul_assoc]
  have heR : (fun p => ∑ k ∈ K, ∑ a ∈ A.product B, ∑ b ∈ A.product B,
        if G k a b then F k a b p else 0) =
      fun p => (Ψ p.1:ℂ)*graphRetainedDirectND A B K G η U W p.1 p.2 := by
    funext p
    simp only [F,graphRetainedDirectND,Finset.mul_sum,mul_ite,mul_zero,mul_assoc]
  have hintF := integrable_finsetSum K (fun k hk => integrable_finsetSum (A.product B)
    (fun a ha => integrable_finsetSum (A.product B) (fun b hb => hiF k hk a ha b hb)))
  have hintR := integrable_finsetSum K (fun k hk => integrable_finsetSum (A.product B)
    (fun a ha => integrable_finsetSum (A.product B) (fun b hb => hiR k hk a ha b hb)))
  rw [heF] at hintF
  rw [heR] at hintR
  have hl := graph_integral_localizationND (volume.prod (μ.prod μ)) A B K G F hiF hε hne
  rw [heF,heR,integral_prod _ hintF,integral_prod _ hintR] at hl
  simp_rw [integral_const_mul] at hl
  have he (r : ℝ) := graphExpandedDirectND_integral μ A B K η U W r
    (hpart.mono (fun _ h => h.2))
  simp_rw [he] at hl
  simp only [← Complex.ofReal_mul] at hl
  rw [integral_complex_ofReal] at hl
  have hb := graphRetainedDirectND_integral_bound μ A B K G η hpart U W hU hW C E hbU hbW
    D hrow hcol hΨ hΨpos
  have hnon : 0 ≤ ∫ r, Ψ r*sourceAngularMomentND μ (fun z => ∑ i ∈ A, U i z) r*
      sourceAngularMomentND μ (fun z => ∑ j ∈ B, W j z) r := integral_nonneg (fun r =>
        mul_nonneg (mul_nonneg (hΨpos r) (sourceAngularMomentND_nonneg _ _ _))
          (sourceAngularMomentND_nonneg _ _ _))
  have htt : ‖((∫ r, Ψ r*sourceAngularMomentND μ (fun z => ∑ i ∈ A, U i z) r*
      sourceAngularMomentND μ (fun z => ∑ j ∈ B, W j z) r : ℝ):ℂ)‖ ≤ ‖(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ)‖ + ‖((∫ r, Ψ r*sourceAngularMomentND μ (fun z => ∑ i ∈ A, U i z) r*
      sourceAngularMomentND μ (fun z => ∑ j ∈ B, W j z) r : ℝ):ℂ)-(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ)‖ := by
    calc
      _ = ‖(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ)+(((∫ r, Ψ r*sourceAngularMomentND μ (fun z => ∑ i ∈ A, U i z) r*
      sourceAngularMomentND μ (fun z => ∑ j ∈ B, W j z) r : ℝ):ℂ)-(∫ r, (Ψ r:ℂ)*∫ z, graphRetainedDirectND A B K G η U W r z ∂μ.prod μ))‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon] at htt
  exact htt.trans (add_le_add hb (by simpa only [mul_assoc] using hl))

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
