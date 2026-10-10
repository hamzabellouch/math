import Mathlib
import OAI.Computability.VertexCover.PCP.QueryIncidence
import OAI.Computability.VertexCover.PCP.InitialGraph

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b «c» => G.accepts e (decode b) (decode «c»)
  reverse_accepts := fun e b «c» => G.reverse_accepts e (decode b) (decode «c»)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

theorem satisfiable_pullback_iff (G : ConstraintGraph V E A)
    (decode : B → A) (encode : A → B) (sectionLaw : ∀ a, decode (encode a) = a) :
    (pullback G decode).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    exact ⟨decode ∘ labeling, h⟩
  · rintro ⟨labeling, h⟩
    refine ⟨encode ∘ labeling, fun e => ?_⟩
    change G.accepts e (decode (encode (labeling (G.tail e))))
      (decode (encode (labeling (G.head e)))) = true
    simpa only [ConstraintGraph.edgeSatisfied, sectionLaw] using h e

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, «c»⟩
  rfl

def initial64 (F : UniqueGames.Foundations.Target.Formula) :
    ConstraintGraph (InitialGraph.CompactVertex F) (InitialGraph.CompactDart F) Label64 :=
  pullback (InitialGraph.build F) decode64

theorem initial64_satisfiable_iff (F : UniqueGames.Foundations.Target.Formula) :
    (initial64 F).Satisfiable ↔ F.Satisfiable :=
  (satisfiable_pullback_iff (InitialGraph.build F) decode64 encode64 decode_encode64).trans
    (InitialGraph.build_satisfiable_iff F)

theorem initial64_alphabet : Fintype.card Label64 = 64 :=
  QueryIncidence.six_query_alphabet

theorem initial64_inverse_size_gap (F : UniqueGames.Foundations.Target.Formula)
    (unsat : ¬ F.Satisfiable) (labeling : InitialGraph.CompactVertex F → Label64) :
    Fintype.card (InitialGraph.CompactDart F) ≤
      (6 * F.clauses.length + 1) * (initial64 F).rejectionCount labeling :=
  InitialGraph.build_inverse_size_gap F unsat (decode64 ∘ labeling)

end UniqueGames.Foundations.PCP.AlphabetRetraction

end OAI
