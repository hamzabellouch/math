import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma upper_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, IsUpperSet (A i)) : IsUpperSet (⋃ i∈s, A i) := by
  intro ω τ h hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨i,hi,hA i hi h hω⟩

lemma finiteWitness_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, HasFiniteOpenWitness (A i)) :
    HasFiniteOpenWitness (⋃ i∈s, A i) := by
  intro ω hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKs,hKA⟩ := hA i hi ω hω
  exact ⟨K,hK,hKs,Set.mem_iUnion₂.mpr ⟨i,hi,hKA⟩⟩

theorem finite_miss_product [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, HasFiniteOpenWitness (A i)) :
    ∏ i∈s, (1-(law q).real (A i)) ≤ 1-(law q).real (⋃ i∈s, A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm := hA i (Finset.mem_insert_self i s)
    have hw' := hw i (Finset.mem_insert_self i s)
    have hs : ∀ j∈s, IsUpperSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hsw : ∀ j∈s, HasFiniteOpenWitness (A j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hind := ih hs hsw
    let B := ⋃ j∈s, A j
    have hBm := upper_biUnion A s hs
    have hBw := finiteWitness_biUnion A s hsw
    have hH := harris_finiteWitness q (A i) B hm hBm hw' hBw
    have hu := measureReal_union_add_inter (s := A i)
      (measurableSet_finiteWitness B hBm hBw) (μ := law q)
      (measure_ne_top _ _) (measure_ne_top _ _)
    have hb : (law q).real (A i)≤1 := measureReal_le_one
    have hp := mul_le_mul_of_nonneg_left hind (by linarith : 0≤1-(law q).real (A i))
    rw [Finset.prod_insert hi]
    rw [Finset.set_biUnion_insert]
    change (1-(law q).real (A i))*(∏ j∈s, (1-(law q).real (A j)))≤
      1-(law q).real (A i∪B)
    change _≤1-(law q).real B at hind
    change _≤(1-(law q).real (A i))*(1-(law q).real B) at hp
    nlinarith

theorem exists_favored_finite [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, HasFiniteOpenWitness (A i)) (a : ℝ) (ha : 0≤a)
    (hu : 1-a^s.card<(law q).real (⋃ i∈s, A i)) :
    ∃ i∈s, 1-a<(law q).real (A i) := by
  by_contra hn
  push Not at hn
  have hp : a^s.card≤∏ i∈s, (1-(law q).real (A i)) := by
    rw [←Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ => ha)
    intro i hi
    linarith [hn i hi]
  have hH := finite_miss_product q A s hA hw
  linarith

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
