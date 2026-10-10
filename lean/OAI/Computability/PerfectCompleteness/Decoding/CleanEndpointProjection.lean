import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionAssembly
import OAI.Computability.PerfectCompleteness.Foundations.SourceOddListsLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanEndpointSlots

namespace OAI

section

namespace PerfectCompleteness.CleanEndpointProjection

open scoped Classical
open RecursiveSpaces MixedSupport SourceQuestionReconstruction

noncomputable section

private theorem reconstruct_designated {I E Q : Type*} {Leaf : I → Type*}
    (designated : (i : I) → Leaf i) (clean : I → Prop) [DecidablePred clean]
    [∀ i, DecidableEq (Leaf i)] (endpoint : I → E → Q)
    (visible : Visible (E := E) designated clean) (own : {i : I // clean i} → Q)
    (i : {i : I // clean i}) :
    reconstruct designated clean endpoint visible own i.val (designated i.val) = own i := by
  exact dite_eq_left ⟨i.property, rfl⟩

private theorem dite_heq_of_pos {α β : Type} {P : Prop} [Decidable P]
    (f : P → α) (g : ¬ P → α) (b : β) (hP : P)
    (h : HEq (f hP) b) : HEq (dite P f g) b := by
  rw [dite_eq_left hP]
  exact h

variable {v m t : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

def sourceProjection (projected : Bool) (e : SourceOddLists.Occurrences m t) :
    ∀ k, Projection (SourceAnswerEquiv.leftSlots clauses (SourceOddLists.left e) k)
      (SourceKeys.slot clauses (rightTuple clauses projected e k)) :=
  match projected with
  | false => fun k => Projection.keep
      (SourceAnswerEquiv.leftSlots clauses (SourceOddLists.left e) k)
  | true => SourceAnswerEquiv.slotProjection clauses e

theorem sourceProjection_of_true (projected : Bool)
    (e : SourceOddLists.Occurrences m t) (k : Fin t) (hp : projected = true) :
    HEq (sourceProjection clauses projected e k)
      (SourceAnswerEquiv.slotProjection clauses e k) := by
  subst projected
  rfl

variable {branch : Nat → Nat} {h : Nat}
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : Visible (E := SourceTuple m t) designated clean)

theorem leftInside_designated
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin m)
    (i : {i : Fin (branch h) // clean i}) :
    CleanEndpointSlots.leftInside clauses designated clean visible own
        (i.val, designated i.val) =
      SourceAnswerEquiv.leftSlots clauses (own i) := by
  funext k
  exact congrArg
    (fun question : Fin t → SourceKeys.Endpoint v m => SourceKeys.slot clauses (question k))
    (reconstruct_designated designated clean (fun _ => leftTuple (v := v)) visible
      (fun j k => SourceKeys.Endpoint.clause (v := v) (own j k)) i)

variable (projected : Fin (branch h) → Bool)

theorem rightInside_designated
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v)
    (i : {i : Fin (branch h) // clean i}) :
    CleanEndpointSlots.rightInside clauses designated clean visible projected own
        (i.val, designated i.val) =
      SourceAnswerEquiv.rightSlots clauses (own i) := by
  funext k
  exact congrArg
    (fun question : Fin t → SourceKeys.Endpoint v m => SourceKeys.slot clauses (question k))
    (reconstruct_designated designated clean (fun j => rightTuple clauses (projected j)) visible
      (fun j k => SourceKeys.Endpoint.variable (m := m) (own j k)) i)

def insideProjection (cleanProjected : ∀ i, clean i → projected i = true)
    (e : {i : Fin (branch h) // clean i} → SourceOddLists.Occurrences m t) :
    ∀ s k, Projection
      (CleanEndpointSlots.leftInside clauses designated clean visible
        (fun i => SourceOddLists.left (e i)) s k)
      (CleanEndpointSlots.rightInside clauses designated clean visible projected
        (fun i => SourceOddLists.right clauses (e i)) s k) :=
  fun s k => if hs : clean s.1 ∧ s.2 = designated s.1 then
    CutProjectionAssembly.castProjection
      (by simp only [SourceAnswerEquiv.leftSlots, SourceOddLists.left,
        CleanEndpointSlots.leftInside, reconstructLeft, reconstruct, dite_eq_left hs])
      (by simp only [rightTuple, cleanProjected s.1 hs.1, ite_true,
        CleanEndpointSlots.rightInside, reconstructRight, reconstruct, dite_eq_left hs,
        SourceOddLists.right])
      (sourceProjection clauses (projected s.1) (e ⟨s.1, hs.1⟩) k)
  else
    CutProjectionAssembly.castProjection
      (by simp only [SourceAnswerEquiv.leftSlots, SourceOddLists.left,
        CleanEndpointSlots.leftInside, reconstructLeft, reconstruct, dite_eq_right hs, leftTuple])
      (by simp only [CleanEndpointSlots.rightInside, reconstructRight, reconstruct, dite_eq_right hs])
      (sourceProjection clauses (projected s.1) (visible s.1 ⟨s.2, hs⟩) k)

theorem insideProjection_designated
    (cleanProjected : ∀ i, clean i → projected i = true)
    (e : {i : Fin (branch h) // clean i} → SourceOddLists.Occurrences m t)
    (i : {i : Fin (branch h) // clean i}) (k : Fin t) :
    HEq (insideProjection clauses designated clean visible projected cleanProjected e
        (i.val, designated i.val) k)
      (SourceAnswerEquiv.slotProjection clauses (e i) k) := by
  refine @dite_heq_of_pos _ _
    (clean i.val ∧ designated i.val = designated i.val) _ _ _
    (SourceAnswerEquiv.slotProjection clauses (e i) k) ⟨i.property, rfl⟩ ?_
  exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
    (sourceProjection_of_true clauses (projected i.val) (e i) k
      (cleanProjected i.val i.property))

end
end PerfectCompleteness.CleanEndpointProjection

end

end OAI
