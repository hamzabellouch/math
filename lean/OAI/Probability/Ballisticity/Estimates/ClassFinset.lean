import Mathlib
import OAI.Probability.Ballisticity.Estimates.FiniteClasses

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace DirectionalTransience

noncomputable def currentClassFinset {d : ℕ} (e : Direction d) (A : CurrentData e) : Finset ℕ :=
  if h : CurrentFiniteClasses e A then h.toFinset else {0}

lemma currentClassFinset_mem {d : ℕ} (e : Direction d) (A : CurrentData e)
    (h : CurrentFiniteClasses e A) (a : ℕ) :
    a∈currentClassFinset e A ↔ ReferenceClasses.representative A.1 a=a := by
  rw [currentClassFinset,dite_eq_left h]
  change a∈(show (Set.range (ReferenceClasses.representative A.1)).Finite from h).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨b,rfl⟩
    exact (ReferenceClasses.representative_eq_iff A.1 _ _).mpr (ReferenceClasses.representative_related A.1 b)
  · intro ha
    exact ⟨a,ha⟩

lemma currentClassFinset_nonempty {d : ℕ} (e : Direction d) (A : CurrentData e) :
    (currentClassFinset e A).Nonempty := by
  by_cases h : CurrentFiniteClasses e A
  · rw [currentClassFinset,dite_eq_left h]
    exact ⟨ReferenceClasses.representative A.1 0,(Set.Finite.mem_toFinset h).mpr (Set.mem_range_self 0)⟩
  · simp [currentClassFinset,h]

lemma currentClassFinset_measurable {d : ℕ} (e : Direction d) : Measurable (currentClassFinset e) := by
  rw [measurable_finset_iff]
  intro a
  apply measurableSet_setOfPred.mp
  have he : {A : CurrentData e | a∈currentClassFinset e A}=
      ({A | CurrentFiniteClasses e A} ∩ {A | ReferenceClasses.representative A.1 a=a}) ∪
      ({A | ¬CurrentFiniteClasses e A} ∩ {A | a=0}) := by
    ext A
    by_cases h : CurrentFiniteClasses e A
    · simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,h,not_true_eq_false,false_and,
        or_false,true_and,currentClassFinset_mem e A h]
    · simp [currentClassFinset,h]
  rw [he]
  exact ((currentFiniteClasses_measurable e).inter
    (measurableSet_eq_fun ((ReferenceClasses.measurable_representative a).comp measurable_fst) measurable_const)).union
    ((currentFiniteClasses_measurable e).compl.inter (by by_cases h : a=0 <;> simp [h]))

lemma currentClassFinset_rep_mem {d : ℕ} (e : Direction d) (A : CurrentData e)
    (h : CurrentFiniteClasses e A) (a : ℕ) :
    ReferenceClasses.representative A.1 a∈currentClassFinset e A := by
  rw [currentClassFinset,dite_eq_left h]
  exact (Set.Finite.mem_toFinset h).mpr (Set.mem_range_self a)

end DirectionalTransience

end

end OAI
