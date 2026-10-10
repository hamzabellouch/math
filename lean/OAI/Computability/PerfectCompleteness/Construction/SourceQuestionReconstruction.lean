import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas

namespace OAI


namespace PerfectCompleteness.SourceQuestionReconstruction

open SourceClause SourceKeys

noncomputable section

variable {I E Q : Type*} {Leaf : I → Type*}
  (designated : (i : I) → Leaf i) (clean : I → Prop) [DecidablePred clean]
  [∀ i, DecidableEq (Leaf i)]

abbrev Visible := (i : I) → {s : Leaf i // ¬(clean i ∧ s = designated i)} → E

def reveal (x : (i : I) → Leaf i → E) : Visible (E := E) designated clean :=
  fun i s => x i s.1

def reconstruct (endpoint : I → E → Q)
    (visible : Visible (E := E) designated clean) (own : {i : I // clean i} → Q) :
    (i : I) → Leaf i → Q :=
  fun i s => if h : clean i ∧ s = designated i then own ⟨i, h.1⟩
    else endpoint i (visible i ⟨s, h⟩)

theorem reconstruct_eq (endpoint : I → E → Q) (x : (i : I) → Leaf i → E) :
    reconstruct designated clean endpoint (reveal designated clean x)
      (fun i => endpoint i.1 (x i.1 (designated i.1))) =
        fun i s => endpoint i (x i s) := by
  funext i s
  by_cases h : clean i ∧ s = designated i
  · simp [reconstruct, h]
  · simp [reconstruct, reveal, h]


variable {v m t : Nat}
  (clauses : Fin m → NormalizedClause v)

abbrev SourceTuple (m t : Nat) := Fin t → Occurrence m

def leftTuple (e : SourceTuple m t) : Fin t → Endpoint v m :=
  fun k => .clause (e k).1

def rightTuple (projected : Bool) (e : SourceTuple m t) : Fin t → Endpoint v m :=
  fun k => if projected then .variable (occurrenceVariable clauses (e k)) else .clause (e k).1

def reconstructLeft
    (visible : Visible (E := SourceTuple m t) designated clean)
    (own : {i : I // clean i} → Fin t → Fin m) :
    (i : I) → Leaf i → Fin t → Endpoint v m :=
  reconstruct designated clean (fun _ => leftTuple) visible
    (fun i k => .clause (own i k))

def reconstructRight (projected : I → Bool)
    (visible : Visible (E := SourceTuple m t) designated clean)
    (own : {i : I // clean i} → Fin t → Fin v) :
    (i : I) → Leaf i → Fin t → Endpoint v m :=
  reconstruct designated clean (fun i => rightTuple clauses (projected i)) visible
    (fun i k => .variable (own i k))

theorem reconstructLeft_eq (x : (i : I) → Leaf i → SourceTuple m t) :
    reconstructLeft designated clean (reveal designated clean x)
      (fun i k => (x i.1 (designated i.1) k).1) =
        fun i s => leftTuple (v := v) (x i s) := by
  exact reconstruct_eq designated clean (fun _ => leftTuple) x

theorem reconstructRight_eq (projected : I → Bool)
    (clean_projected : ∀ i, clean i → projected i = true)
    (x : (i : I) → Leaf i → SourceTuple m t) :
    reconstructRight designated clean clauses projected (reveal designated clean x)
      (fun i k => occurrenceVariable clauses (x i.1 (designated i.1) k)) =
        fun i s => rightTuple clauses (projected i) (x i s) := by
  have hown : (fun (i : {i : I // clean i}) k =>
      Endpoint.variable (m := m) (occurrenceVariable clauses (x i.1 (designated i.1) k))) =
      (fun (i : {i : I // clean i}) =>
        rightTuple clauses (projected i.1) (x i.1 (designated i.1))) := by
    funext i k
    simp only [rightTuple, clean_projected i.1 i.2, ite_true]
  unfold reconstructRight
  rw [hown]
  exact reconstruct_eq designated clean (fun i => rightTuple clauses (projected i)) x

theorem reconstructRight_slots (projected : I → Bool)
    (clean_projected : ∀ i, clean i → projected i = true)
    (x : (i : I) → Leaf i → SourceTuple m t) :
    (fun i s k => slot clauses
      (reconstructRight designated clean clauses projected (reveal designated clean x)
        (fun i k => occurrenceVariable clauses (x i.1 (designated i.1) k)) i s k)) =
      (fun i s k => slot clauses (rightTuple clauses (projected i) (x i s) k)) := by
  rw [reconstructRight_eq designated clean clauses projected clean_projected x]

end
end PerfectCompleteness.SourceQuestionReconstruction

end OAI
