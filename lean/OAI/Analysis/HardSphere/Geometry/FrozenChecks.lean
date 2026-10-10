import Mathlib
import OAI.Analysis.HardSphere.Geometry.AuxiliaryChecks

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

def freezeOutside (U : Finset I) (x y : ∀i,X i) : ∀i,X i :=
  fun i ↦ if i∈U then y i else x i
omit [Fintype I] in
lemma freezeOutside_measurable (U : Finset I) (x : ∀i,X i) : Measurable (freezeOutside U x) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈U
  · simpa only [freezeOutside,ite_eq_left hi] using (measurable_pi_apply i)
  · simp only [freezeOutside,ite_eq_right hi]
    exact measurable_const

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_update (U : Finset I) (x y : ∀i,X i) {i : I} (hi : i∈U) (v : X i) :
    freezeOutside U x (Function.update y i v)=Function.update (freezeOutside U x y) i v := by
  funext j
  by_cases hj : j=i
  · subst j;simp [freezeOutside,hi]
  · simp [freezeOutside,Function.update_of_ne hj]

def FrozenCheckIndex (checks : C → LocalCheck X) (U : Finset I) :=
  {c : C // ((checks c).support∩U).Nonempty}

instance (checks : C → LocalCheck X) (U : Finset I) : Fintype (FrozenCheckIndex checks U) :=
  by
    classical
    unfold FrozenCheckIndex
    infer_instance

def frozenChecks (checks : C → LocalCheck X) (U : Finset I) (x : ∀i,X i) :
    FrozenCheckIndex checks U → LocalCheck X := fun c ↦ {
  support := (checks c.val).support∩U
  nonempty := c.property
  arity := (Finset.card_le_card Finset.inter_subset_left).trans (checks c.val).arity
  pass := fun y ↦ (checks c.val).pass (freezeOutside U x y)
  measurable_pass := (checks c.val).measurable_pass.preimage (freezeOutside_measurable U x)
  depends := by
    intro y z hyz
    apply (checks c.val).depends
    intro i hi
    by_cases hu : i∈U
    · simp only [freezeOutside,ite_eq_left hu]
      exact hyz i (Finset.mem_inter.mpr ⟨hi,hu⟩)
    · simp only [freezeOutside,ite_eq_right hu]
}

omit [Fintype C]
lemma frozen_support_subset (checks : C → LocalCheck X) (U t : Finset I) (c : C) :
    (checks c).support ⊆ t∪(Finset.univ \ U) ↔ (checks c).support∩U ⊆t := by
  constructor
  · intro h i hi
    rcases Finset.mem_union.mp (h (Finset.mem_inter.mp hi).1) with ht|ho
    · exact ht
    · exact False.elim ((Finset.mem_sdiff.mp ho).2 (Finset.mem_inter.mp hi).2)
  · intro h i hi
    by_cases hu : i∈U
    · exact Finset.mem_union_left _ (h (Finset.mem_inter.mpr ⟨hi,hu⟩))
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩)

lemma frozen_retained (checks : C → LocalCheck X) (U t : Finset I) (x y : ∀i,X i)
    (hx : x∈retainedEvent checks (Finset.univ \ U)) :
    y∈retainedEvent (frozenChecks checks U x) t ↔
      freezeOutside U x y∈retainedEvent checks (t∪(Finset.univ \ U)) := by
  constructor
  · intro hy c hc
    by_cases he : ((checks c).support∩U).Nonempty
    · exact hy ⟨c,he⟩ ((frozen_support_subset checks U t c).mp hc)
    · have hout : (checks c).support⊆Finset.univ \ U := by
        intro i hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
        intro hu
        exact he ⟨i,Finset.mem_inter.mpr ⟨hi,hu⟩⟩
      apply ((checks c).depends x (freezeOutside U x y) ?_).mp (hx c hout)
      intro i hi
      simp only [freezeOutside,ite_eq_right (Finset.mem_sdiff.mp (hout hi)).2]
  · intro hy c hc
    exact hy c.val ((frozen_support_subset checks U t c.val).mpr hc)

lemma frozen_checkWeight (checks : C → LocalCheck X) (U t : Finset I) (x y : ∀i,X i)
    (hx : x∈retainedEvent checks (Finset.univ \ U)) :
    checkWeight (frozenChecks checks U x) t y=
      checkWeight checks (t∪(Finset.univ \ U)) (freezeOutside U x y) := by
  classical
  simp only [checkWeight,Set.indicator_apply,frozen_retained checks U t x y hx]

lemma frozen_insertion (checks : C → LocalCheck X) (U s : Finset I) (x y : ∀i,X i) (i : I) :
    freezeOutside U x y∈insertionEvent checks (s∪(Finset.univ \ U)) i →
      y∈insertionEvent (frozenChecks checks U x) s i := by
  intro hy c hc hcs
  apply hy c.val
  · rw [←Finset.insert_union]
    exact (frozen_support_subset checks U (insert i s) c.val).mpr hc
  · intro hs
    exact hcs ((frozen_support_subset checks U s c.val).mp hs)

lemma frozen_uniformInsertion (checks : C → LocalCheck X) (U : Finset I) (x : ∀i,X i)
    (μ : ∀i,Measure (X i)) {a : ℝ≥0∞}
    (h : UniformInsertionOn checks μ a U) :
    UniformInsertionOn (frozenChecks checks U x) μ a U := by
  intro i hi s his y
  have hin : i∉s∪(Finset.univ \ U) := by simp [Finset.mem_union,his,hi]
  apply (h i hi (s∪(Finset.univ \ U)) hin (freezeOutside U x y)).trans
  apply lintegral_mono
  intro v
  dsimp only
  rw [←freezeOutside_update U x y hi v]
  by_cases hp : freezeOutside U x (Function.update y i v)∈insertionEvent checks (s∪(Finset.univ \ U)) i
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (frozen_insertion checks U s x (Function.update y i v) i hp)]
  · rw [Set.indicator_of_notMem hp]
    exact bot_le

end HardSphere.Comparison

end
end

end

end OAI
