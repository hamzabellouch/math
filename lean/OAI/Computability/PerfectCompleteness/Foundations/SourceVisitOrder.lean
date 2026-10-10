import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceVisitOrder

open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m : Nat}

def visitOrder (branch : Nat → Nat) (n t m : Nat) :
    List (PreliminarySampler.Questions branch n t m) :=
  (SourceQuestionOrder.sourceOrder branch n t m).reverse

theorem visitOrder_eq_tupleOrder (branch : Nat → Nat) (n t m : Nat) :
    visitOrder branch n t m =
      (MachineTupleOdometer.tupleOrder m (TreeCanonical.locationCount branch n t)).map
        SourceQuestionOrder.tupleToQuestion := by
  simp only [visitOrder, SourceQuestionOrder.sourceOrder, ← List.map_reverse,
    List.reverse_reverse]

@[simp] theorem visitOrder_reverse (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).reverse = SourceQuestionOrder.sourceOrder branch n t m := by
  simp only [visitOrder, List.reverse_reverse]

@[simp] theorem visitOrder_length (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).length = m ^ TreeCanonical.locationCount branch n t := by
  simp only [visitOrder, List.length_reverse, SourceQuestionOrder.sourceOrder_length]

theorem visitOrder_nodup (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).Nodup :=
  List.nodup_reverse.mpr (SourceQuestionOrder.sourceOrder_nodup branch n t m)

theorem mem_visitOrder (question : PreliminarySampler.Questions branch n t m) :
    question ∈ visitOrder branch n t m := by
  simpa only [visitOrder, List.mem_reverse] using SourceQuestionOrder.mem_sourceOrder question

@[simp] theorem visitOrder_toFinset (branch : Nat → Nat) (n t m : Nat) :
    (visitOrder branch n t m).toFinset = Finset.univ := by
  ext question
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_visitOrder question

theorem sum_map_visitOrder {A : Type*} [AddCommMonoid A]
    (f : PreliminarySampler.Questions branch n t m → A) :
    ((visitOrder branch n t m).map f).sum = ∑ question, f question := by
  rw [visitOrder, List.map_reverse, List.sum_reverse]
  exact SourceQuestionOrder.sum_map_sourceOrder f

theorem output_eq_reverse_visitOrder (branch : Nat → Nat) (n t m : Nat) :
    TupleIndexMachine.output (TreeCanonical.locationCount branch n t) m =
      (visitOrder branch n t m).reverse.flatMap
        (fun question => encodeWords (SourceQuestionOrder.numberedClauseIDs question)) := by
  rw [visitOrder_reverse]
  exact SourceQuestionOrder.output_eq_sourceOrder branch n t m

end

end PerfectCompleteness.SourceVisitOrder

end

end OAI
