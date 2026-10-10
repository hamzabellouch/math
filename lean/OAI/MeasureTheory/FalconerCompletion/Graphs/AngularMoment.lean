import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphChildSquare
import OAI.MeasureTheory.FalconerCompletion.Graphs.ProfileChildCard
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ENNReal ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

noncomputable def sourceAngularMomentND (μ : Measure V) (U : ℝ × V → ℂ) (r : ℝ) : ℝ :=
  ∫ w, ‖U (r,w)‖^2 ∂μ

noncomputable def sourceAngularHND (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) : ℝ :=
  (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r

noncomputable def sourceAngularHFND (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) : ℝ :=
  (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ∫ r, Ψ (r/(2:ℝ)^v)*‖∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ‖^2

lemma graph_radial_normalizationND {Ω : ℝ} (hΩ : 0 < Ω) (Ψ f : ℝ → ℝ) :
    Ω⁻¹*(∫ r, Ψ (r/Ω)*f r) = ∫ u, Ψ u*f (Ω*u) := by
  have h := Measure.integral_comp_mul_left (fun r => Ψ (r/Ω)*f r) Ω
  simp only [abs_of_pos (inv_pos.mpr hΩ),smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_div_cancel_left₀ u hΩ.ne']

lemma sourceAngularHND_normalized (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) :
    sourceAngularHND d μ a v Ψ U W = (2:ℝ)^((d:ℝ)*(v-a))*
      ∫ u, Ψ u*sourceAngularMomentND μ U ((2:ℝ)^v*u)*sourceAngularMomentND μ W ((2:ℝ)^v*u) := by
  dsimp [sourceAngularHND]
  rw [mul_assoc]
  congr 1
  simpa only [mul_assoc] using graph_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v)
    Ψ (fun r => sourceAngularMomentND μ U r*sourceAngularMomentND μ W r)

lemma sourceAngularHFND_normalized (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) :
    sourceAngularHFND d μ a v Ψ ψ U W = (2:ℝ)^((d:ℝ)*(v-a))*
      ∫ u, Ψ u*‖∫ w, ψ w*U ((2:ℝ)^v*u,w)*conj (W ((2:ℝ)^v*u,w)) ∂μ‖^2 := by
  dsimp [sourceAngularHFND]
  rw [mul_assoc,graph_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v)]

lemma sourceAngularMomentND_measurable (μ : Measure V) [SFinite μ]
    {U : ℝ × V → ℂ} (hU : Measurable U) : Measurable (sourceAngularMomentND μ U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

lemma sourceAngularMomentND_nonneg (μ : Measure V) (U : ℝ × V → ℂ) (r : ℝ) :
    0 ≤ sourceAngularMomentND μ U r := integral_nonneg (fun _ => sq_nonneg _)

lemma sourceAngularMomentND_bound (μ : Measure V) [IsFiniteMeasure μ]
    (U : ℝ × V → ℂ) {C : ℝ} (r : ℝ) (hb : ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C) :
    sourceAngularMomentND μ U r ≤ C^2*μ.real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hb] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma angular_square_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {f : V → ℂ} (hf : Measurable f) {C : ℝ} (hb : ∀ᵐ w ∂μ, ‖f w‖ ≤ C) :
    Integrable (fun w => ‖f w‖^2) μ := by
  apply Integrable.of_bound (hf.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards [hb] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma graph_weighted_moments_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {U W : ℝ × V → ℂ} (hU : Measurable U) (hW : Measurable W)
    {C D : ℝ} (hUbound : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C)
    (hWbound : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖ ≤ D)
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) :
    Integrable (fun r => Ψ r*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r) := by
  apply (hΨ.norm.mul_const ((C^2*μ.real univ)*(D^2*μ.real univ))).mono'
    ((hΨ.aestronglyMeasurable.mul (sourceAngularMomentND_measurable μ hU).aestronglyMeasurable).mul
      (sourceAngularMomentND_measurable μ hW).aestronglyMeasurable)
  filter_upwards with r
  change ‖Ψ r*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r‖ ≤ _
  rw [norm_mul,norm_mul,Real.norm_eq_abs (sourceAngularMomentND μ U r),
    Real.norm_eq_abs (sourceAngularMomentND μ W r),
    abs_of_nonneg (sourceAngularMomentND_nonneg μ U r),
    abs_of_nonneg (sourceAngularMomentND_nonneg μ W r),mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (sourceAngularMomentND_bound μ U r (hUbound r))
    (sourceAngularMomentND_bound μ W r (hWbound r)) (sourceAngularMomentND_nonneg μ W r)
      (by positivity)) (norm_nonneg _)

lemma sourceAngularMomentND_pair (μ : Measure V) [SFinite μ]
    (U W : ℝ × V → ℂ) (r : ℝ) :
    (∫ w : V × V, ‖U (r,w.1)*W (r,w.2)‖^2 ∂μ.prod μ) =
      sourceAngularMomentND μ U r*sourceAngularMomentND μ W r := by
  simp_rw [norm_mul,mul_pow]
  exact integral_prod_mul (fun w => ‖U (r,w)‖^2) (fun w => ‖W (r,w)‖^2)

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
open scoped BigOperators ComplexConjugate
theorem finset_bipartite_schur {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (u : α → ℝ) (v : β → ℝ) (d : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ d)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ d) :
    (∑ a ∈ A, ∑ b ∈ B, if G a b then u a*v b else 0) ≤
      d/2*((∑ a ∈ A, u a^2)+(∑ b ∈ B, v b^2)) := by
  have hp (a : α) (b : β) : 2*(if G a b then u a*v b else 0) ≤
      (if G a b then u a^2 else 0)+(if G a b then v b^2 else 0) := by
    split_ifs
    · nlinarith [sq_nonneg (u a-v b)]
    · norm_num
  have hs := Finset.sum_le_sum (s := A) (fun a _ =>
    Finset.sum_le_sum (s := B) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hR : (∑ a ∈ A, ∑ b ∈ B, if G a b then u a^2 else 0) ≤ d*(∑ a ∈ A, u a^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  have hC : (∑ a ∈ A, ∑ b ∈ B, if G a b then v b^2 else 0) ≤ d*(∑ b ∈ B, v b^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  nlinarith

lemma graph_discarded_sumND {ι : Type*} (S : Finset ι) (G : ι → Prop)
    [DecidablePred G] (K : ι → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hK : ∀ i ∈ S, ¬G i → ‖K i‖ ≤ ε) :
    ‖(∑ i ∈ S, K i)-(∑ i ∈ S.filter G, K i)‖ ≤ S.card*ε := by
  classical
  have he : (∑ i ∈ S, K i)-(∑ i ∈ S.filter G, K i) =
      ∑ i ∈ S.filter (fun i => ¬G i), K i := by
    have h := Finset.sum_filter_add_sum_filter_not S G K
    linear_combination -h
  rw [he]
  calc
    _ ≤ ∑ i ∈ S.filter (fun i => ¬G i), ‖K i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S.filter (fun i => ¬G i), ε := Finset.sum_le_sum
      (fun i hi => hK i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
    _ ≤ S.card*ε := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le S _) hε

lemma graph_complex_schurND {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (F : α → ℂ) (H : β → ℂ) (D : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ D)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ D) :
    ‖∑ a ∈ A, ∑ b ∈ B, if G a b then F a*conj (H b) else 0‖ ≤
      D/2*((∑ a ∈ A, ‖F a‖^2)+(∑ b ∈ B, ‖H b‖^2)) := by
  calc
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, if G a b then ‖F a‖*‖H b‖ else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs <;> simp
    _ ≤ _ := finset_bipartite_schur A B G (fun a => ‖F a‖) (fun b => ‖H b‖) D hrow hcol

lemma graph_partition_schurND {α β κ : Type*} (A : Finset α) (B : Finset β)
    (C : Finset κ) (G : κ → α → β → Prop) [∀ k, DecidableRel (G k)]
    (F : α → ℂ) (H : β → ℂ) (η : κ → ℝ)
    (hη : ∀ k ∈ C, 0 ≤ η k) (hpart : ∑ k ∈ C, η k=1) (D : ℝ)
    (hrow : ∀ k ∈ C, ∀ a ∈ A, ((B.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ C, ∀ b ∈ B, ((A.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ C, (η k:ℂ)*(∑ a ∈ A, ∑ b ∈ B, if G k a b then F a*conj (H b) else 0)‖ ≤
      D/2*((∑ a ∈ A, ‖F a‖^2)+(∑ b ∈ B, ‖H b‖^2)) := by
  calc
    _ ≤ ∑ k ∈ C, η k*(D/2*((∑ a ∈ A, ‖F a‖^2)+(∑ b ∈ B, ‖H b‖^2))) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hη k hk)]
      exact mul_le_mul_of_nonneg_left (graph_complex_schurND A B (G k) F H D
        (hrow k hk) (hcol k hk)) (hη k hk)
    _ = _ := by rw [← Finset.sum_mul,hpart,one_mul]

lemma graph_product_square_sumND {α β : Type*} (A : Finset α) (B : Finset β)
    (U : α → ℂ) (V : β → ℂ) :
    (∑ z ∈ A.product B, ‖U z.1*V z.2‖^2) =
      (∑ a ∈ A, ‖U a‖^2)*(∑ b ∈ B, ‖V b‖^2) := by
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [norm_mul,mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

lemma graph_partition_product_schurND {α β κ : Type*} (A : Finset α) (B : Finset β)
    (C : Finset κ) (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (U₁ U₂ : α → ℂ) (V₁ V₂ : β → ℂ) (η : κ → ℝ)
    (hη : ∀ k ∈ C, 0 ≤ η k) (hpart : ∑ k ∈ C, η k=1) (D : ℝ)
    (hrow : ∀ k ∈ C, ∀ a ∈ A.product B, (((A.product B).filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ C, ∀ b ∈ A.product B, (((A.product B).filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ C, (η k:ℂ)*(∑ a ∈ A.product B, ∑ b ∈ A.product B,
      if G k a b then (U₁ a.1*V₁ a.2)*conj (U₂ b.1*V₂ b.2) else 0)‖ ≤
      D/2*((∑ a ∈ A, ‖U₁ a‖^2)*(∑ b ∈ B, ‖V₁ b‖^2)+
        (∑ a ∈ A, ‖U₂ a‖^2)*(∑ b ∈ B, ‖V₂ b‖^2)) := by
  simpa only [graph_product_square_sumND] using graph_partition_schurND
    (A.product B) (A.product B) C G (fun z => U₁ z.1*V₁ z.2) (fun z => U₂ z.1*V₂ z.2)
    η hη hpart D hrow hcol

lemma graph_pair_partitionND {κ : Type*} (C : Finset κ) (η₁ η₂ : κ → ℝ)
    (h₁ : ∑ k ∈ C, η₁ k=1) (h₂ : ∑ k ∈ C, η₂ k=1) :
    ∑ k ∈ C.product C, η₁ k.1*η₂ k.2=1 := by
  rw [Finset.product_eq_sprod,Finset.sum_product,← Finset.sum_mul_sum,h₁,h₂,one_mul]

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

noncomputable def graphChildSquareND (A : Finset α) (B : Finset β)
    (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ) (r : ℝ) (z : V × V) : ℝ :=
  (∑ i ∈ A, ‖U i (r,z.1)‖^2)*(∑ j ∈ B, ‖W j (r,z.2)‖^2)

lemma graphChildSquareND_integrable (μ : Measure V) [IsFiniteMeasure μ]
    (A : Finset α) (B : Finset β) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i ∈ A, Measurable (U i)) (hW : ∀ j ∈ B, Measurable (W j))
    (C : α → ℝ) (D : β → ℝ)
    (hbU : ∀ i ∈ A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖ ≤ C i)
    (hbW : ∀ j ∈ B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖ ≤ D j) (r : ℝ) :
    Integrable (graphChildSquareND A B U W r) (μ.prod μ) := by
  unfold graphChildSquareND
  apply Integrable.mul_prod (f := fun w => ∑ i ∈ A, ‖U i (r,w)‖^2)
    (g := fun w => ∑ j ∈ B, ‖W j (r,w)‖^2)
  · exact integrable_finsetSum A (fun i hi => angular_square_integrableND μ
      ((hU i hi).comp (measurable_const.prodMk measurable_id)) (hbU i hi r))
  · exact integrable_finsetSum B (fun j hj => angular_square_integrableND μ
      ((hW j hj).comp (measurable_const.prodMk measurable_id)) (hbW j hj r))

lemma graphChildSquareND_integral (μ : Measure V) [IsFiniteMeasure μ]
    (A : Finset α) (B : Finset β) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (hU : ∀ i ∈ A, Measurable (U i)) (hW : ∀ j ∈ B, Measurable (W j))
    (C : α → ℝ) (D : β → ℝ)
    (hbU : ∀ i ∈ A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖ ≤ C i)
    (hbW : ∀ j ∈ B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖ ≤ D j) (r : ℝ) :
    (∫ z, graphChildSquareND A B U W r z ∂μ.prod μ) =
      ∑ i ∈ A, ∑ j ∈ B, sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r := by
  dsimp [graphChildSquareND]
  rw [integral_prod_mul (fun w => ∑ i ∈ A, ‖U i (r,w)‖^2)
    (fun w => ∑ j ∈ B, ‖W j (r,w)‖^2),integral_finsetSum A (f := fun i w => ‖U i (r,w)‖^2) (fun i hi => angular_square_integrableND μ
    ((hU i hi).comp (measurable_const.prodMk measurable_id)) (hbU i hi r)),
    integral_finsetSum B (f := fun j w => ‖W j (r,w)‖^2) (fun j hj => angular_square_integrableND μ
    ((hW j hj).comp (measurable_const.prodMk measurable_id)) (hbW j hj r))]
  exact Finset.sum_mul_sum A B _ _

noncomputable def graphRetainedCrossedND (A : Finset α) (B : Finset β) (K : Finset κ)
    (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (η : κ → V × V → ℝ) (U : α → ℝ × V → ℂ) (W : β → ℝ × V → ℂ)
    (r : ℝ) (z : V × V) : ℂ :=
  ∑ k ∈ K, (η k z:ℂ)*(∑ a ∈ A.product B, ∑ b ∈ A.product B,
    if G k a b then (U a.1 (r,z.1)*W a.2 (r,z.2))*
      conj (U b.1 (r,z.2)*W b.2 (r,z.1)) else 0)

lemma graphRetainedCrossedND_angular_bound (μ : Measure V) [IsFiniteMeasure μ]
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
    ‖∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ‖ ≤
      D*∑ i ∈ A, ∑ j ∈ B, sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r := by
  have hi := graphChildSquareND_integrable μ A B U W hU hW C E hbU hbW r
  have hb := norm_integral_le_of_norm_le ((hi.add hi.swap).const_mul (D/2))
    (show ∀ᵐ z ∂μ.prod μ, ‖graphRetainedCrossedND A B K G η U W r z‖ ≤
      D/2*(graphChildSquareND A B U W r z+graphChildSquareND A B U W r z.swap) from by
      filter_upwards [hpart] with z hz
      exact graph_partition_product_schurND A B K G
        (fun i => U i (r,z.1)) (fun i => U i (r,z.2))
        (fun j => W j (r,z.2)) (fun j => W j (r,z.1)) (fun k => η k z) hz.1 hz.2 D hrow hcol)
  simp only [Pi.add_apply,Function.comp_apply] at hb
  rw [integral_const_mul] at hb
  have hadd := integral_add hi hi.swap
  simp only [Function.comp_apply] at hadd
  rw [hadd,integral_prod_swap] at hb
  rw [graphChildSquareND_integral μ A B U W hU hW C E hbU hbW] at hb
  convert hb using 1
  ring

theorem graphRetainedCrossedND_integral_bound (μ : Measure V) [IsFiniteMeasure μ]
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
    ‖∫ r, (Ψ r:ℂ)*∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ‖ ≤
      D*∑ i ∈ A, ∑ j ∈ B, ∫ r, Ψ r*sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r := by
  have hi (i) (hi : i ∈ A) (j) (hj : j ∈ B) :=
    graph_weighted_moments_integrableND μ (hU i hi) (hW j hj) (hbU i hi) (hbW j hj) hΨ
  have hs := (integrable_finsetSum A (fun i hiA => integrable_finsetSum B
    (fun j hjB => hi i hiA j hjB))).const_mul D
  have hh := norm_integral_le_of_norm_le hs
    (show ∀ᵐ r : ℝ, ‖(Ψ r:ℂ)*∫ z, graphRetainedCrossedND A B K G η U W r z ∂μ.prod μ‖ ≤
      D*∑ i ∈ A, ∑ j ∈ B, Ψ r*sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r from by
      filter_upwards with r
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hΨpos r)]
      have hp := mul_le_mul_of_nonneg_left (graphRetainedCrossedND_angular_bound
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

end OAI
