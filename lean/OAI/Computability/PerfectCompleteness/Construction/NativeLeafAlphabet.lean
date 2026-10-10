import OAI.Computability.PerfectCompleteness.Foundations.SourceOddListsLemmas

namespace OAI

section

namespace PerfectCompleteness.NativeLeafAlphabet

open SourceClause

variable {I : Type*} {v m t : Nat}

def castAssignment {a b : I → MixedSupport.Slot} (h : a = b) :
    MixedSupport.Assignment a ≃ MixedSupport.Assignment b :=
  Equiv.cast (congrArg (fun slots : I → MixedSupport.Slot =>
    MixedSupport.Assignment slots) h)

@[simp] theorem castAssignment_rfl (a : I → MixedSupport.Slot) :
    castAssignment (rfl : a = a) = Equiv.refl (MixedSupport.Assignment a) := rfl

def nativeLeftEquiv (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) {a : Fin t → MixedSupport.Slot}
    (ha : a = SourceAnswerEquiv.leftSlots clauses question) :
    MixedSupport.Assignment a ≃ SourceOddLists.LeftLabels t :=
  (castAssignment ha).trans (SourceAnswerEquiv.leftEquiv clauses question)

def nativeRightEquiv (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin v) {b : Fin t → MixedSupport.Slot}
    (hb : b = SourceAnswerEquiv.rightSlots clauses question) :
    MixedSupport.Assignment b ≃ SourceOddLists.RightLabels t :=
  (castAssignment hb).trans (SourceAnswerEquiv.rightEquiv clauses question)

theorem projection_encode (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) {a b : Fin t → MixedSupport.Slot}
    (ha : a = SourceAnswerEquiv.leftSlots clauses (SourceOddLists.left e))
    (hb : b = SourceAnswerEquiv.rightSlots clauses (SourceOddLists.right clauses e))
    (q : ∀ k, MixedSupport.Projection (a k) (b k))
    (hq : ∀ k, HEq (q k) (SourceAnswerEquiv.slotProjection clauses e k))
    (x : MixedSupport.Assignment a) :
    nativeRightEquiv clauses (SourceOddLists.right clauses e) hb
        (MixedSupport.projectionMap q x) =
      SourceOddLists.projection clauses e
        (nativeLeftEquiv clauses (SourceOddLists.left e) ha x) := by
  subst a
  subst b
  have hprojection : q = SourceAnswerEquiv.slotProjection clauses e := by
    funext k
    exact eq_of_heq (hq k)
  subst q
  exact SourceAnswerEquiv.projection_encode clauses e x

end PerfectCompleteness.NativeLeafAlphabet

end

end OAI
