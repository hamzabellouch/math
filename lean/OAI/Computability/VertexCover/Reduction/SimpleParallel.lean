import Mathlib
import OAI.Computability.VertexCover.Reduction.RejectionCount

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection
open UniqueGames.Foundations.Target

def Consistent (F : Formula) (i : Fin F.clauses.length) (P : Pattern) : Prop :=
  ∀ k l : Fin 3, (literalAt F i k).variableIndex = (literalAt F i l).variableIndex →
    flipSign (literalAt F i k).positive (P.val k) =
      flipSign (literalAt F i l).positive (P.val l)

instance (F : Formula) (i : Fin F.clauses.length) (P : Pattern) :
    Decidable (Consistent F i P) := inferInstanceAs (Decidable (∀ _k _l, _ → _))

theorem consistent_truth (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) (hp : ∃ k, clauseValue F a i k = true) :
    Consistent F i ⟨clauseValue F a i, hp⟩ := by
  intro k l hkl
  change flipSign _ (flipSign _ _) = flipSign _ (flipSign _ _)
  simp only [flipSign_flipSign]
  rw [hkl]

def defaultAssignment (F : Formula) (i : Fin F.clauses.length)
    (v : Fin F.«variables») : Bool :=
  if v = (literalAt F i 0).variableIndex then (literalAt F i 0).positive else false

theorem default_true (F : Formula) (i : Fin F.clauses.length) :
    clauseValue F (defaultAssignment F i) i 0 = true := by
  simp only [clauseValue, Literal.eval, defaultAssignment, ↓reduceIte]
  cases (literalAt F i 0).positive <;> rfl

def defaultPattern (F : Formula) (i : Fin F.clauses.length) : Pattern :=
  ⟨clauseValue F (defaultAssignment F i) i, ⟨0, default_true F i⟩⟩

def normalizePattern (F : Formula) (i : Fin F.clauses.length) (P : Pattern) : Pattern :=
  if Consistent F i P then P else defaultPattern F i

theorem normalize_consistent (F : Formula) (i : Fin F.clauses.length) (P : Pattern) :
    Consistent F i (normalizePattern F i P) := by
  unfold normalizePattern
  split
  · assumption
  · exact consistent_truth F (defaultAssignment F i) i _

theorem normalize_truth (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) (hp : ∃ k, clauseValue F a i k = true) :
    normalizePattern F i ⟨clauseValue F a i, hp⟩ = ⟨clauseValue F a i, hp⟩ := by
  exact ite_eq_left (consistent_truth F a i hp)

noncomputable def normalizeLabel (F : Formula) (i : Fin F.clauses.length) (l : Fin 7) : Fin 7 :=
  patternEquiv (normalizePattern F i (patternEquiv.symm l))

noncomputable def simpleGame (F : Formula) (hne : F.clauses ≠ []) : LabelCover :=
  { game F hne with projection := fun e label =>
      (game F hne).projection e (normalizeLabel F ((game F hne).left e) label) }

noncomputable def decodedLabeling (F : Formula) (hne : F.clauses ≠ [])
    (A : (simpleGame F hne).Labeling) : (game F hne).Labeling :=
  (fun i => normalizeLabel F i (A.1 i), A.2)

theorem simple_satisfies_iff (F : Formula) (hne : F.clauses ≠ [])
    (A : (simpleGame F hne).Labeling) (e : Fin (simpleGame F hne).M) :
    (simpleGame F hne).Satisfies A e ↔ (game F hne).Satisfies (decodedLabeling F hne A) e :=
  Iff.rfl

theorem simple_perfect_complete (F : Formula) (hne : F.clauses ≠ []) (hF : F.Satisfiable) :
    ∃ A : (simpleGame F hne).Labeling, ∀ e, (simpleGame F hne).Satisfies A e := by
  obtain ⟨a, ha⟩ := hF
  let A : (simpleGame F hne).Labeling := honestLabeling F hne a ha
  refine ⟨A, ?_⟩
  intro e
  change (game F hne).Satisfies (decodedLabeling F hne A) e
  have hdecode : decodedLabeling F hne A = honestLabeling F hne a ha := by
    apply Prod.ext
    · change (fun i : Fin F.clauses.length => normalizeLabel F i
        (patternEquiv ⟨clauseValue F a i, _⟩)) =
        (fun i : Fin F.clauses.length => patternEquiv ⟨clauseValue F a i, _⟩)
      funext i
      simp only [normalizeLabel, Equiv.symm_apply_apply, normalize_truth]
    · rfl
  rw [hdecode]
  exact honest_satisfies F hne a ha e

theorem simple_rejection_count (F : Formula) (hne : F.clauses ≠ [])
    (A : (simpleGame F hne).Labeling) :
    (unsatisfiedClauses F (assignmentOf F hne (decodedLabeling F hne A))).card ≤
      (Finset.univ.filter (fun e => ¬(simpleGame F hne).Satisfies A e)).card :=
  rejection_count F hne (decodedLabeling F hne A)

theorem simple_parallel (F : Formula) (hne : F.clauses ≠ [])
    (e e' : Fin (simpleGame F hne).M)
    (hl : (simpleGame F hne).left e = (simpleGame F hne).left e')
    (hr : (simpleGame F hne).right e = (simpleGame F hne).right e') :
    (simpleGame F hne).projection e = (simpleGame F hne).projection e' := by
  funext label
  change (finProdFinEquiv.symm e).1 = (finProdFinEquiv.symm e').1 at hl
  change (literalAt F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).variableIndex =
    (literalAt F (finProdFinEquiv.symm e').1 (finProdFinEquiv.symm e').2).variableIndex at hr
  simp only [simpleGame, game, normalizeLabel, Equiv.symm_apply_apply]
  rw [hl] at hr ⊢
  congr 1
  exact normalize_consistent F (finProdFinEquiv.symm e').1 (patternEquiv.symm label) _ _ hr

end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
