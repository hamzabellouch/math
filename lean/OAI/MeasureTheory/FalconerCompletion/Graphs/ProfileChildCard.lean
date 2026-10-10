import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.ExistsFarSeparationPower

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ENNReal

lemma profile_child_cardND {V α : Type*} [MeasurableSpace V]
    (μ : Measure V) [IsFiniteMeasure μ] (A : Finset α) (cell : α → Set V) (parent : Set V)
    (hdisj : (A : Set α).PairwiseDisjoint cell)
    (hm : ∀ i ∈ A, MeasurableSet (cell i)) (hsub : ∀ i ∈ A, cell i ⊆ parent)
    {R ma mp err : ℝ} (hR : 0 < R)
    (hlower : ∀ i ∈ A, R^(-mp-err) ≤ (μ (cell i)).toReal)
    (hupper : (μ parent).toReal ≤ R^(-ma+err)) :
    (A.card:ℝ) ≤ R^(mp-ma+2*err) := by
  have hsum : (A.card:ℝ)*R^(-mp-err) ≤ (μ parent).toReal := by
    calc
      _ = ∑ _i ∈ A, R^(-mp-err) := by simp
      _ ≤ ∑ i ∈ A, (μ (cell i)).toReal := Finset.sum_le_sum hlower
      _ = (μ (⋃ i ∈ A, cell i)).toReal := by
        rw [measure_biUnion_finset hdisj hm,ENNReal.toReal_sum]
        intro i _; exact measure_ne_top _ _
      _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (iUnion₂_subset hsub))
  have hmul : (A.card:ℝ)*R^(-mp-err) ≤ R^(-ma+err) := hsum.trans hupper
  have he : R^(mp-ma+2*err)*R^(-mp-err)=R^(-ma+err) := by
    rw [← Real.rpow_add hR]; congr 1; ring
  rw [← he] at hmul
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hR _)).mp hmul

lemma profile_pair_cardND {V α β : Type*} [MeasurableSpace V]
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Finset α) (B : Finset β) (cell₁ : α → Set V) (cell₂ : β → Set V) (X Y : Set V)
    (hd₁ : (A : Set α).PairwiseDisjoint cell₁) (hd₂ : (B : Set β).PairwiseDisjoint cell₂)
    (hm₁ : ∀ i ∈ A, MeasurableSet (cell₁ i)) (hm₂ : ∀ j ∈ B, MeasurableSet (cell₂ j))
    (hs₁ : ∀ i ∈ A, cell₁ i ⊆ X) (hs₂ : ∀ j ∈ B, cell₂ j ⊆ Y)
    {R ma₁ ma₂ mp₁ mp₂ err₁ err₂ : ℝ} (hR : 0<R)
    (hl₁ : ∀ i ∈ A, R^(-mp₁-err₁) ≤ (μ (cell₁ i)).toReal)
    (hl₂ : ∀ j ∈ B, R^(-mp₂-err₂) ≤ (ν (cell₂ j)).toReal)
    (hu₁ : (μ X).toReal ≤ R^(-ma₁+err₁)) (hu₂ : (ν Y).toReal ≤ R^(-ma₂+err₂)) :
    (A.card:ℝ)*B.card ≤ R^((mp₁-ma₁)+(mp₂-ma₂)+2*(err₁+err₂)) := by
  calc
    _ ≤ R^(mp₁-ma₁+2*err₁)*R^(mp₂-ma₂+2*err₂) :=
      mul_le_mul (profile_child_cardND μ A cell₁ X hd₁ hm₁ hs₁ hR hl₁ hu₁)
        (profile_child_cardND ν B cell₂ Y hd₂ hm₂ hs₂ hR hl₂ hu₂)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Metric

theorem farSeparatedGridND_pair_card {d : ℕ} (b : ℕ) {K : ℝ} (hK : 0≤K)
    (P : Finset ((Fin d → ℤ) × (Fin d → ℤ))) (A : Finset (Fin d → ℤ))
    (hA : ∀ p∈P, p.1∈A) (hP : ∀ p∈P, farSeparatedGridND b K p.1 p.2) :
    (P.card:ℝ)≤A.card*(8*K+5)^d := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) hA
  have hf (X : Fin d → ℤ) : ((P.filter (fun p => p.1=X)).card:ℝ)≤(8*K+5)^d := by
    let F := P.filter (fun p => p.1=X)
    have hi : Set.InjOn Prod.snd (F : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
      intro p hp q hq hpq
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) hpq
    have hh := farSeparatedGridND_partner_card b hK X (F.image Prod.snd) (by
      intro Y hY
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hY
      have hp' := Finset.mem_filter.mp hp
      simpa only [← hp'.2] using hP p hp'.1)
    rw [Finset.card_image_of_injOn hi] at hh
    exact hh
  calc
    _ = ∑ X∈A, ((P.filter (fun p => p.1=X)).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _X∈A, (8*K+5)^d := Finset.sum_le_sum (fun X _ => hf X)
    _ = _ := by simp

theorem far_profile_quadruple_cardND {d : ℕ} (b : ℕ) {K : ℝ} (hK : 0≤K)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (A B : Finset (Fin d → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin d)))
    (hA : ∀ p∈P, p.1∈A) (hB : ∀ q∈Q, q.1∈B)
    (hP : ∀ p∈P, farSeparatedGridND b K p.1 p.2)
    (hQ : ∀ q∈Q, farSeparatedGridND b K q.1 q.2)
    (hs₁ : ∀ i∈A, ambientGridCell b i⊆X) (hs₂ : ∀ j∈B, ambientGridCell b j⊆Y)
    {R ma₁ ma₂ mb₁ mb₂ err₁ err₂ : ℝ} (hR : 0<R)
    (hl₁ : ∀ i∈A, R^(-mb₁-err₁)≤(μ (ambientGridCell b i)).toReal)
    (hl₂ : ∀ j∈B, R^(-mb₂-err₂)≤(ν (ambientGridCell b j)).toReal)
    (hu₁ : (μ X).toReal≤R^(-ma₁+err₁)) (hu₂ : (ν Y).toReal≤R^(-ma₂+err₂)) :
    ((P.product Q).card:ℝ)≤(8*K+5)^(2*d)*R^((mb₁-ma₁)+(mb₂-ma₂)+2*(err₁+err₂)) := by
  have hdisj (S : Finset (Fin d → ℤ)) : (S : Set (Fin d → ℤ)).PairwiseDisjoint (ambientGridCell b) := by
    intro i _ j _ hij
    exact ambientGridCell_disjoint hij
  have hprof := profile_pair_cardND μ ν A B (ambientGridCell b) (ambientGridCell b) X Y
    (hdisj A) (hdisj B) (fun i _ => measurableSet_ambientGridCell b i)
    (fun j _ => measurableSet_ambientGridCell b j) hs₁ hs₂ hR hl₁ hl₂ hu₁ hu₂
  have hpp := farSeparatedGridND_pair_card b hK P A hA hP
  have hqq := farSeparatedGridND_pair_card b hK Q B hB hQ
  calc
    ((P.product Q).card:ℝ) = (P.card:ℝ)*Q.card := by exact_mod_cast Finset.card_product P Q
    _ ≤ (A.card*(8*K+5)^d)*(B.card*(8*K+5)^d) :=
      mul_le_mul hpp hqq (Nat.cast_nonneg _) (by positivity)
    _ = ((8*K+5)^d*(8*K+5)^d)*((A.card:ℝ)*B.card) := by ring
    _ ≤ ((8*K+5)^d*(8*K+5)^d)*R^((mb₁-ma₁)+(mb₂-ma₂)+2*(err₁+err₂)) :=
      mul_le_mul_of_nonneg_left hprof (by positivity)
    _ = _ := by rw [← pow_add,← two_mul]

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Metric

def gridPairSetND {d : ℕ} (b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  ambientGridCell b p.1 ×ˢ ambientGridCell b p.2

lemma gridPairSetND_measurable {d : ℕ} (b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    MeasurableSet (gridPairSetND b p) :=
  (measurableSet_ambientGridCell b p.1).prod (measurableSet_ambientGridCell b p.2)

lemma gridPairSetND_disjoint {d b : ℕ} {p q : (Fin d → ℤ) × (Fin d → ℤ)} (hpq : p≠q) :
    Disjoint (gridPairSetND b p) (gridPairSetND b q) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hpq
  apply Prod.ext
  · by_contra hn
    exact Set.disjoint_left.mp (ambientGridCell_disjoint hn) hx.1 hy.1
  · by_contra hn
    exact Set.disjoint_left.mp (ambientGridCell_disjoint hn) hx.2 hy.2

noncomputable def gridPairMeasureND {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  (ρ.prod ρ).restrict (gridPairSetND b p)

instance gridPairMeasureND_finite {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    IsFiniteMeasure (gridPairMeasureND ρ b p) := by
  unfold gridPairMeasureND
  infer_instance

lemma gridPairMeasureND_eq_prod {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    gridPairMeasureND ρ b p=(ρ.restrict (ambientGridCell b p.1)).prod
      (ρ.restrict (ambientGridCell b p.2)) := by
  exact (Measure.prod_restrict _ _).symm

lemma gridPairMeasureND_mass {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    (gridPairMeasureND ρ b p).real univ=(ρ (ambientGridCell b p.1)).toReal*
      (ρ (ambientGridCell b p.2)).toReal := by
  rw [gridPairMeasureND_eq_prod]
  rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  simp only [Measure.restrict_apply_univ, ENNReal.toReal_mul]

theorem gridPairMeasureND_sum_mass {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (b : ℕ) (P : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (hsub : ∀ p∈P, ambientGridCell b p.1⊆X ∧ ambientGridCell b p.2⊆X) :
    ∑ p∈P, (gridPairMeasureND ρ b p).real univ≤(ρ X).toReal^2 := by
  have hd : (P : Set ((Fin d → ℤ) × (Fin d → ℤ))).PairwiseDisjoint (gridPairSetND b) := by
    intro p _ q _ hpq
    exact gridPairSetND_disjoint hpq
  have he : ∑ p∈P, (gridPairMeasureND ρ b p).real univ=
      ((ρ.prod ρ) (⋃ p∈P, gridPairSetND b p)).toReal := by
    rw [measure_biUnion_finset hd (fun p _ => gridPairSetND_measurable b p),ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro p _
      simp only [gridPairMeasureND,measureReal_def,Measure.restrict_apply_univ]
    · intro p _; exact measure_ne_top _ _
  rw [he]
  have hs : (⋃ p∈P, gridPairSetND b p)⊆X×ˢX := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact ⟨(hsub p hp).1 hz.1,(hsub p hp).2 hz.2⟩
  calc
    _ ≤ ((ρ.prod ρ) (X×ˢX)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs)
    _ = _ := by rw [Measure.prod_prod,ENNReal.toReal_mul]; ring

theorem gridPairMeasureND_quadruple_mass {d : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (b : ℕ) (P Q : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (X Y : Set (EuclideanSpace ℝ (Fin d)))
    (hP : ∀ p∈P, ambientGridCell b p.1⊆X ∧ ambientGridCell b p.2⊆X)
    (hQ : ∀ q∈Q, ambientGridCell b q.1⊆Y ∧ ambientGridCell b q.2⊆Y) :
    ∑ z∈P.product Q, ((gridPairMeasureND ρ b z.1).prod (gridPairMeasureND κ b z.2)).real univ≤
      (ρ X).toReal^2*(κ Y).toReal^2 := by
  have hm (p q : (Fin d → ℤ) × (Fin d → ℤ)) :
      ((gridPairMeasureND ρ b p).prod (gridPairMeasureND κ b q)).real univ=
      (gridPairMeasureND ρ b p).real univ*(gridPairMeasureND κ b q).real univ := by
    rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
    exact ENNReal.toReal_mul
  simp_rw [hm]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum]
  exact mul_le_mul (gridPairMeasureND_sum_mass ρ b P X hP)
    (gridPairMeasureND_sum_mass κ b Q Y hQ) (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)) (sq_nonneg _)

theorem gridPairMeasureND_integral_quad_partition {d : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (b : ℕ) (P Q : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (F : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) → ℂ)
    (hF : Integrable F ((ρ.prod ρ).prod (κ.prod κ))) :
    (∫ z in (⋃ pq∈P.product Q, gridPairSetND b pq.1 ×ˢ gridPairSetND b pq.2), F z
      ∂(ρ.prod ρ).prod (κ.prod κ)) =
      ∑ pq∈P.product Q, ∫ z, F z ∂(gridPairMeasureND ρ b pq.1).prod (gridPairMeasureND κ b pq.2) := by
  have hd : ((P.product Q) : Set (((Fin d → ℤ) × (Fin d → ℤ)) × ((Fin d → ℤ) × (Fin d → ℤ)))).PairwiseDisjoint
      (fun pq => gridPairSetND b pq.1 ×ˢ gridPairSetND b pq.2) := by
    intro p _ q _ hpq
    apply Set.disjoint_left.mpr
    intro z hp hq
    apply hpq
    apply Prod.ext
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.1 hq.1
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.2 hq.2
  rw [integral_biUnion_finset _ (fun pq _ => (gridPairSetND_measurable b pq.1).prod
    (gridPairSetND_measurable b pq.2)) hd (fun _ _ => hF.integrableOn)]
  apply Finset.sum_congr rfl
  intro pq _
  rw [← Measure.prod_restrict]
  rfl

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
