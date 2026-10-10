import OAI.Probability.BenjaminiSchramm.PeakFiniteEnergy
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BernoulliProduct
variable {E ι : Type*} [Countable E]

lemma harris_finiteWitness_compl (q : E → unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : HasFiniteOpenWitness A) (hwB : HasFiniteOpenWitness B) :
    (law q).real Aᶜ*(law q).real Bᶜ ≤ (law q).real (Aᶜ ∩ Bᶜ) := by
  have hmA := measurableSet_finiteWitness A hA hwA
  have hmB := measurableSet_finiteWitness B hB hwB
  have hh := harris_finiteWitness q A B hA hB hwA hwB
  have hu := measureReal_union_add_inter (μ := law q) (s := A) hmB
    (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_compl hmA,measureReal_compl hmB,←Set.compl_union,
    measureReal_compl (hmA.union hmB),probReal_univ]
  nlinarith

def finiteBadUnion (F : Finset ι) (A : ι → Set (Set E)) : Set (Set E) :=
  {ω | ∃ i ∈ F, ω ∈ A i}

omit [Countable E] in
lemma finiteBadUnion_upper (F : Finset ι) (A : ι → Set (Set E))
    (hA : ∀ i ∈ F, IsUpperSet (A i)) : IsUpperSet (finiteBadUnion F A) := by
  rintro ω η hωη ⟨i,hi,hω⟩
  exact ⟨i,hi,hA i hi hωη hω⟩

omit [Countable E] in
lemma finiteBadUnion_finiteWitness (F : Finset ι) (A : ι → Set (Set E))
    (hw : ∀ i ∈ F, HasFiniteOpenWitness (A i)) : HasFiniteOpenWitness (finiteBadUnion F A) := by
  rintro ω ⟨i,hi,hω⟩
  obtain ⟨S,hS,hSω,hSA⟩ := hw i hi ω hω
  exact ⟨S,hS,hSω,i,hi,hSA⟩

theorem finite_avoidance_product (q : E → unitInterval) (F : Finset ι)
    (A : ι → Set (Set E)) (hA : ∀ i ∈ F, IsUpperSet (A i))
    (hw : ∀ i ∈ F, HasFiniteOpenWitness (A i)) :
    (∏ i ∈ F, (law q).real (A i)ᶜ) ≤ (law q).real (finiteBadUnion F A)ᶜ := by
  induction F using Finset.induction_on with
  | empty =>
    have he : finiteBadUnion (∅ : Finset ι) A=∅ := by ext ω; simp [finiteBadUnion]
    simp only [Finset.prod_empty,he,Set.compl_empty,probReal_univ,le_refl]
  | @insert i F hi ih =>
    have hAF : ∀ j ∈ F, IsUpperSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hwF : ∀ j ∈ F, HasFiniteOpenWitness (A j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hh := harris_finiteWitness_compl q (A i) (finiteBadUnion F A)
      (hA i (Finset.mem_insert_self _ _)) (finiteBadUnion_upper F A hAF)
        (hw i (Finset.mem_insert_self _ _)) (finiteBadUnion_finiteWitness F A hwF)
    have he : finiteBadUnion (insert i F) A=A i ∪ finiteBadUnion F A := by
      ext ω
      simp only [finiteBadUnion,Set.mem_ofPred_eq,Finset.mem_insert,Set.mem_union]
      aesop
    rw [Finset.prod_insert hi,he,Set.compl_union]
    exact (mul_le_mul_of_nonneg_left (ih hAF hwF) measureReal_nonneg).trans hh

theorem exponential_finite_avoidance (q : E → unitInterval) (F : Finset ι)
    (A : ι → Set (Set E)) (hA : ∀ i ∈ F, IsUpperSet (A i))
    (hw : ∀ i ∈ F, HasFiniteOpenWitness (A i)) (g : ι → ℝ)
    (hbound : ∀ i ∈ F, Real.exp (-g i) ≤ (law q).real (A i)ᶜ) :
    ENNReal.ofReal (Real.exp (-(∑ i ∈ F, g i))) ≤ law q (finiteBadUnion F A)ᶜ := by
  apply ENNReal.ofReal_le_of_le_toReal
  calc
    _ = ∏ i ∈ F, Real.exp (-g i) := by rw [←Real.exp_sum,Finset.sum_neg_distrib]
    _ ≤ ∏ i ∈ F, (law q).real (A i)ᶜ :=
      Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos (-g i)).le) hbound
    _ ≤ _ := finite_avoidance_product q F A hA hw

end CriticalPercolation.BernoulliProduct

end

end OAI
