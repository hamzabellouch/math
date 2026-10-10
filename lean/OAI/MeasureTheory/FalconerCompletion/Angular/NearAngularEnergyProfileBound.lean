import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.NearRetained
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteHFBound2
import OAI.MeasureTheory.FalconerCompletion.Graphs.ProfileChildCard2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
variable {V : Type*} [MeasurableSpace V]

theorem nearAngularEnergyND_profile_bound (d : ℕ) {N : ℕ} (hN : 0<N)
    (μ : Measure V) [IsFiniteMeasure μ]
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℝ) (h : ℕ) (v ma mb err : ℝ)
    (A B : Finset (Fin d → ℤ)) (hAB : (A.product B).Nonempty)
    (X Y : Set (EuclideanSpace ℝ (Fin d)))
    (hs₁ : ∀ i∈A, ambientGridCell h i⊆X) (hs₂ : ∀ j∈B, ambientGridCell h j⊆Y)
    (hl₁ : ∀ i∈A, ((2:ℝ)^N)^(-mb-err)≤(ρ (ambientGridCell h i)).toReal)
    (hl₂ : ∀ j∈B, ((2:ℝ)^N)^(-mb-err)≤(κ (ambientGridCell h j)).toReal)
    (hu₁ : (ρ X).toReal≤((2:ℝ)^N)^(-ma+err))
    (hu₂ : (κ Y).toReal≤((2:ℝ)^N)^(-ma+err))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (hΨpos : ∀ r, 0≤Ψ r) :
    nearAngularEnergyND d μ a h v (((2:ℝ)^N)^(-(mb-ma)))
      (((2:ℝ)^N)^(-(mb-ma))) Ψ A B U W ≤
      (20*(d+1:ℝ)+5)^(2*d)*((2:ℝ)^N)^(-2*((mb-(d:ℝ)*(h:ℝ)/(2*N))-
        (ma-(d:ℝ)*a/(2*N)))+4*err)*graphChildMaxND d μ h v Ψ A B hAB U W := by
  let R : ℝ := (2:ℝ)^N
  let D : ℝ := (20*(d+1:ℝ)+5)^(2*d)
  let Δ : ℝ := (mb-ma)-(d/2:ℝ)*((h:ℝ)-a)/(N:ℝ)
  have hR : 0<R := by positivity
  have hdisj (S : Finset (Fin d → ℤ)) : (S : Set (Fin d → ℤ)).PairwiseDisjoint
      (ambientGridCell h) := by
    intro i _ j _ hij
    exact ambientGridCell_disjoint hij
  have hlabels := profile_pair_cardND ρ κ A B (ambientGridCell h) (ambientGridCell h) X Y
    (hdisj A) (hdisj B) (fun i _ => measurableSet_ambientGridCell h i)
    (fun j _ => measurableSet_ambientGridCell h j) hs₁ hs₂ hR hl₁ hl₂ hu₁ hu₂
  have he : Δ+Δ+(d:ℝ)*((h:ℝ)-a)/(N:ℝ)+4*err = (mb-ma)+(mb-ma)+2*(err+err) := by
    dsimp [Δ]
    ring
  have hlabel' : (A.card:ℝ)*B.card≤R^(Δ+Δ+(d:ℝ)*((h:ℝ)-a)/(N:ℝ)+4*err) := by
    rw [he]
    exact hlabels
  have hc := graph_profile_coefficient_leND hN d a h Δ Δ (4*err) 0
    (D := D) (C := D) (L := (A.card:ℝ)*B.card) (by dsimp [D]; positivity)
    (by simp) hlabel'
  have hi : Δ+(d:ℝ)/2*((h:ℝ)-a)/(N:ℝ)=mb-ma := by dsimp [Δ]; ring
  have hd : -(Δ+Δ)+0+4*err = -2*((mb-(d:ℝ)*(h:ℝ)/(2*N))-
      (ma-(d:ℝ)*a/(2*N)))+4*err := by dsimp [Δ]; ring
  rw [hi,hd] at hc
  have hh := nearAngularEnergyND_le_sum d μ a h v (R^(-(mb-ma))) (R^(-(mb-ma)))
    A B U W hU hW C E hbU hbW hΨ hΨpos
  have hs := graphChild_sum_le_maxND d μ h v Ψ A B hAB U W
  have hm := graphChildMaxND_nonneg d μ h v Ψ hΨpos A B hAB U W
  apply hh.trans
  calc
    _ ≤ ((R^(-(mb-ma)))^2*(R^(-(mb-ma)))^2*(2:ℝ)^((d:ℝ)*((h:ℝ)-a))*D)*
        (((A.card:ℝ)*B.card)*graphChildMaxND d μ h v Ψ A B hAB U W) :=
      mul_le_mul_of_nonneg_left hs (by dsimp [D]; positivity)
    _ = ((R^(-(mb-ma)))^2*(R^(-(mb-ma)))^2*(2:ℝ)^((d:ℝ)*((h:ℝ)-a))*D*
        ((A.card:ℝ)*B.card))*graphChildMaxND d μ h v Ψ A B hAB U W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hm

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
variable {V : Type*} [MeasurableSpace V]

lemma angular_four_term_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {U₁ U₂ W₁ W₂ : ℝ × V → ℂ}
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hW₁ : Measurable W₁) (hW₂ : Measurable W₂) {C₁ C₂ E₁ E₂ : ℝ}
    (hbU₁ : ∀ r, ∀ᵐ w ∂μ, ‖U₁ (r,w)‖≤C₁)
    (hbU₂ : ∀ r, ∀ᵐ w ∂μ, ‖U₂ (r,w)‖≤C₂)
    (hbW₁ : ∀ r, ∀ᵐ w ∂μ, ‖W₁ (r,w)‖≤E₁)
    (hbW₂ : ∀ r, ∀ᵐ w ∂μ, ‖W₂ (r,w)‖≤E₂)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ) :
    Integrable (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*
      ((U₁ (p.1,p.2.1)*W₁ (p.1,p.2.2))*
        conj (U₂ (p.1,p.2.1)*W₂ (p.1,p.2.2)))) (volume.prod (μ.prod μ)) := by
  let F : ℝ × (V × V) → ℂ := fun p =>
    (U₁ (p.1,p.2.1)*W₁ (p.1,p.2.2))*conj (U₂ (p.1,p.2.1)*W₂ (p.1,p.2.2))
  let M : ℝ := (|C₁| * |E₁|) * (|C₂| * |E₂|)
  have hf : Measurable F := by dsimp [F]; fun_prop
  have hm : Measurable (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*F p) := by fun_prop
  have hb : ∀ᵐ p : ℝ × (V × V) ∂volume.prod (μ.prod μ), ‖F p‖≤M := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hf.norm measurable_const)).mpr
    filter_upwards with r
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      ((hf.comp (measurable_const.prodMk measurable_id)).norm) measurable_const)).mpr
    filter_upwards [hbU₁ r,hbU₂ r] with w₁ hw₁ hw₂
    filter_upwards [hbW₁ r,hbW₂ r] with w₂ hv₁ hv₂
    dsimp [F,M]
    simp only [norm_mul,Complex.norm_conj]
    exact mul_le_mul
      (mul_le_mul (hw₁.trans (le_abs_self _)) (hv₁.trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _))
      (mul_le_mul (hw₂.trans (le_abs_self _)) (hv₂.trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _)) (by positivity) (by positivity)
  apply ((hΨ.norm.comp_fst (μ.prod μ)).mul_const M).mono' hm.aestronglyMeasurable
  filter_upwards [hb] with p hp
  simp only [norm_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)

theorem nearRetainedND_joint_integrable {d : ℕ} (h : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ) :
    Integrable (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*nearRetainedND h A B U W p.1 p.2)
      (volume.prod (μ.prod μ)) := by
  simp only [nearRetainedND_eq,Finset.mul_sum]
  apply integrable_finsetSum
  intro a ha
  apply integrable_finsetSum
  intro b hb
  obtain ⟨ha₁,ha₂⟩ := Finset.mem_product.mp ha
  obtain ⟨hb₁,hb₂⟩ := Finset.mem_product.mp hb
  by_cases hab : nearGridPairND h a b
  · simp only [hab,ite_true]
    exact angular_four_term_integrableND μ (hU a.1 ha₁) (hU b.1 hb₁)
      (hW a.2 ha₂) (hW b.2 hb₂) (hbU a.1 ha₁) (hbU b.1 hb₁)
      (hbW a.2 ha₂) (hbW b.2 hb₂) hmΨ hΨ
  · simp only [hab,ite_false,mul_zero]
    exact integrable_zero _ _ _

theorem nearRetainedND_integral_prod {d : ℕ} (h : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ) :
    (∫ p : ℝ × (V × V), (Ψ p.1:ℂ)*nearRetainedND h A B U W p.1 p.2
      ∂volume.prod (μ.prod μ)) =
      ∫ r, (Ψ r:ℂ)*∫ z, nearRetainedND h A B U W r z ∂μ.prod μ := by
  rw [integral_prod _ (nearRetainedND_joint_integrable h μ A B U W hU hW C E hbU hbW hmΨ hΨ)]
  simp only [integral_const_mul]

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
variable {V : Type*} [MeasurableSpace V]

noncomputable def farRetainedND {d : ℕ} (h : ℕ) (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ) (r : ℝ) (z : V × V) : ℂ :=
  ∑ a ∈ A.product B, ∑ b ∈ A.product B, if nearGridPairND h a b then 0 else
    (U a.1 (r,z.1)*W a.2 (r,z.2))*conj (U b.1 (r,z.1)*W b.2 (r,z.2))

omit [MeasurableSpace V] in
lemma near_far_completeND {d : ℕ} (h : ℕ) (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ) (r : ℝ) (z : V × V) :
    nearRetainedND h A B U W r z + farRetainedND h A B U W r z =
      ((‖∑ i ∈ A, U i (r,z.1)‖^2*‖∑ j ∈ B, W j (r,z.2)‖^2:ℝ):ℂ) := by
  rw [nearRetainedND_eq,farRetainedND,← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have he (a b : (Fin d → ℤ) × (Fin d → ℤ)) (q : ℂ) :
      (if nearGridPairND h a b then q else 0)+(if nearGridPairND h a b then 0 else q)=q := by
    split_ifs <;> simp
  simp_rw [he]
  rw [graph_four_sumND A B (fun i => U i (r,z.1)) (fun i => U i (r,z.1))
    (fun j => W j (r,z.2)) (fun j => W j (r,z.2)),
    Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_mul,mul_pow]

theorem farRetainedND_joint_integrable {d : ℕ} (h : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ) :
    Integrable (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*farRetainedND h A B U W p.1 p.2)
      (volume.prod (μ.prod μ)) := by
  simp only [farRetainedND,Finset.mul_sum]
  apply integrable_finsetSum
  intro a ha
  apply integrable_finsetSum
  intro b hb
  obtain ⟨ha₁,ha₂⟩ := Finset.mem_product.mp ha
  obtain ⟨hb₁,hb₂⟩ := Finset.mem_product.mp hb
  by_cases hab : nearGridPairND h a b
  · simp only [hab,ite_true,mul_zero]
    exact integrable_zero _ _ _
  · simp only [hab,ite_false]
    exact angular_four_term_integrableND μ (hU a.1 ha₁) (hU b.1 hb₁)
      (hW a.2 ha₂) (hW b.2 hb₂) (hbU a.1 ha₁) (hbU b.1 hb₁)
      (hbW a.2 ha₂) (hbW b.2 hb₂) hmΨ hΨ

theorem near_far_integral_identityND {d : ℕ} (h : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ) :
    ((∫ r, Ψ r*sourceAngularMomentND μ (fun p => ∑ i∈A, U i p) r*
      sourceAngularMomentND μ (fun p => ∑ j∈B, W j p) r : ℝ):ℂ) =
      (∫ p : ℝ × (V × V), (Ψ p.1:ℂ)*nearRetainedND h A B U W p.1 p.2
        ∂volume.prod (μ.prod μ)) +
      (∫ p : ℝ × (V × V), (Ψ p.1:ℂ)*farRetainedND h A B U W p.1 p.2
        ∂volume.prod (μ.prod μ)) := by
  have hin := nearRetainedND_joint_integrable h μ A B U W hU hW C E hbU hbW hmΨ hΨ
  have hif := farRetainedND_joint_integrable h μ A B U W hU hW C E hbU hbW hmΨ hΨ
  rw [← integral_add hin hif]
  have he : (fun p : ℝ × (V × V) => (Ψ p.1:ℂ)*nearRetainedND h A B U W p.1 p.2+
      (Ψ p.1:ℂ)*farRetainedND h A B U W p.1 p.2) =
      fun p => (Ψ p.1:ℂ)*((‖∑ i∈A, U i (p.1,p.2.1)‖^2*
        ‖∑ j∈B, W j (p.1,p.2.2)‖^2:ℝ):ℂ) := by
    funext p
    rw [← mul_add,near_far_completeND]
  have hi := hin.add hif
  change Integrable (fun p : ℝ × (V × V) =>
    (Ψ p.1:ℂ)*nearRetainedND h A B U W p.1 p.2+
      (Ψ p.1:ℂ)*farRetainedND h A B U W p.1 p.2) (volume.prod (μ.prod μ)) at hi
  rw [he] at hi ⊢
  rw [integral_prod _ hi]
  have hp (r : ℝ) : (∫ z : V × V, ‖∑ i∈A, U i (r,z.1)‖^2*
      ‖∑ j∈B, W j (r,z.2)‖^2 ∂μ.prod μ) =
      sourceAngularMomentND μ (fun p => ∑ i∈A, U i p) r*
        sourceAngularMomentND μ (fun p => ∑ j∈B, W j p) r :=
    integral_prod_mul (fun w => ‖∑ i∈A, U i (r,w)‖^2)
      (fun w => ‖∑ j∈B, W j (r,w)‖^2)
  simp only [integral_const_mul,integral_complex_ofReal,hp,← Complex.ofReal_mul,mul_assoc]

theorem sourceAngularHND_near_far_bound (d : ℕ) (h : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (a v lam₁ lam₂ : ℝ)
    (A B : Finset (Fin d → ℤ)) (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0≤Ψ r) :
    sourceAngularHND d μ a v Ψ (fun p => lam₁ • ∑ i∈A, U i p)
        (fun p => lam₂ • ∑ j∈B, W j p) ≤
      nearAngularEnergyND d μ a h v lam₁ lam₂ Ψ A B U W +
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
        ‖∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*farRetainedND h A B U W p.1 p.2
          ∂volume.prod (μ.prod μ)‖ := by
  have hm : Measurable (fun r : ℝ => Ψ (r/(2:ℝ)^v)) := by fun_prop
  have he := near_far_integral_identityND h μ A B U W hU hW C E hbU hbW hm hΨ
  have hn : 0≤∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ (fun p => ∑ i∈A, U i p) r*
      sourceAngularMomentND μ (fun p => ∑ j∈B, W j p) r := by
    apply integral_nonneg
    intro r
    exact mul_nonneg (mul_nonneg (hΨpos _) (sourceAngularMomentND_nonneg _ _ _))
      (sourceAngularMomentND_nonneg _ _ _)
  have hh := norm_add_le
    (∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*nearRetainedND h A B U W p.1 p.2
      ∂volume.prod (μ.prod μ))
    (∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*farRetainedND h A B U W p.1 p.2
      ∂volume.prod (μ.prod μ))
  rw [← he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn] at hh
  rw [nearRetainedND_integral_prod h μ A B U W hU hW C E hbU hbW hm hΨ] at hh
  have hs := mul_le_mul_of_nonneg_left hh
    (show 0≤lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹ by positivity)
  rw [sourceAngularHND_smul]
  simpa only [sourceAngularHND,nearAngularEnergyND,mul_add,mul_assoc] using hs

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
