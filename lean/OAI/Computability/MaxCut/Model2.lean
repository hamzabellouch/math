import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
Finite occurrence presentations used by the v2 rounding/subdivision construction.
An occurrence has its own identifier: its endpoints need not be distinct and
different occurrences may have the same endpoints. The bipartite target records
injectivity of the pair of endpoints, which is precisely the required simplicity.
No hardness or analytic premise enters these structures.
-/

namespace MaxCutGames.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

structure BipartiteGame (L R E A : Type*) where
  left : E → L
  right : E → R
  permutation : E → Equiv.Perm A
  simple : Function.Injective (fun e => (left e, right e))

namespace OccurrenceGame

def Satisfied {V E A : Type*} (G : OccurrenceGame V E A)
    (labeling : V → A) (e : E) : Prop :=
  labeling (G.target e) = G.permutation e (labeling (G.source e))

instance satisfiedDecidable {V E A : Type*} [DecidableEq A]
    (G : OccurrenceGame V E A) (labeling : V → A) (e : E) :
    Decidable (G.Satisfied labeling e) := inferInstanceAs (Decidable (_ = _))

def IsTranslation {V E A : Type*} [Add A] (G : OccurrenceGame V E A) : Prop :=
  ∃ offset : E → A, ∀ e a, G.permutation e a = a + offset e

end OccurrenceGame

namespace BipartiteGame

def Satisfied {L R E A : Type*} (G : BipartiteGame L R E A)
    (leftLabeling : L → A) (rightLabeling : R → A) (e : E) : Prop :=
  rightLabeling (G.right e) = G.permutation e (leftLabeling (G.left e))

instance satisfiedDecidable {L R E A : Type*} [DecidableEq A]
    (G : BipartiteGame L R E A) (a : L → A) (b : R → A) (e : E) :
    Decidable (G.Satisfied a b e) := inferInstanceAs (Decidable (_ = _))

def IsTranslation {L R E A : Type*} [Add A] (G : BipartiteGame L R E A) : Prop :=
  ∃ offset : E → A, ∀ e a, G.permutation e a = a + offset e

end BipartiteGame

end MaxCutGames.Explicit

end OAI
