import Mathlib.GroupTheory.FreeGroup.Reduce

namespace OAI
noncomputable section
namespace CuntzPureness

def canonicalFreeWord {X : Type*} (g : FreeGroup X) : List (X × Bool) :=
  @FreeGroup.toWord X (Classical.decEq X) g

lemma freeGroup_toWord_eq_canonical {X : Type*} [d : DecidableEq X] (g : FreeGroup X) :
    g.toWord = canonicalFreeWord g :=
  congrArg (fun e => @FreeGroup.toWord X e g) (Subsingleton.elim d (Classical.decEq X))
end CuntzPureness

end

end OAI
