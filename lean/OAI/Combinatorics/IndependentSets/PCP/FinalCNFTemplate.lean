import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.VerifierCNF

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalTemplates (accepted : Bool) (bits : Fin 12 → Bool) : List LiteralTemplate :=
  (templates accepted bits).flatMap fun c => [(c)[0], (c)[1], (c)[2]]

theorem literalTemplates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (literalTemplates accepted bits).length = 30 := by
  unfold literalTemplates
  rw [VerifierToCNF.length_flatMap_constant _ _ 3 (by intro c hc; rfl), templates_length]

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

theorem words_length (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) :
    (words accepted bits index).length = 60 := by
  unfold words
  rw [VerifierToCNF.length_flatMap_constant _ _ 6
    (by intro c hc; simp [clauseWords, literalWords]), templates_length]

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def resolve : Reference → Fin (VerifierToCNF.outputVariables V)
  | .query i => VerifierToCNF.oldIndex V (V.query e i)
  | .auxiliary j => VerifierToCNF.freshIndex V e p j

theorem resolve_query_value (i : Fin 12) :
    (resolve V e p (.query i)).val = (V.query e i).val := by
  simp only [resolve, VerifierToCNF.oldIndex, Fin.val_castAdd]

theorem resolve_auxiliary_value (j : Fin 9) :
    (resolve V e p (.auxiliary j)).val =
      V.«variables» + ((e.val * 4096 + p.val) * 9 + j.val) := by
  change (VerifierToCNF.freshIndex V e p j).val = _
  exact (VerifierToCNF.freshIndex_value V e p j).trans
    (congrArg (fun k : Nat => V.«variables» + ((e.val * k + p.val) * 9 + j.val))
      (show (VerifierToCNF.patterns 12).length = 4096 from VerifierToCNF.patterns_length 12))

def instantiateLiteral (literal : LiteralTemplate) : Literal (VerifierToCNF.outputVariables V) :=
  ⟨resolve V e p literal.reference, literal.positive⟩

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiate_templates_of_acceptance (accepted : Bool)
    (h : V.accepts e (VerifierToCNF.patternAt 12 p) = accepted) :
    (templates accepted (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
      VerifierToCNF.block V (by decide) e p := by
  rw [← h]
  exact instantiate_templates V e p

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

theorem block_words_length :
    ((VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords).length = 60 := by
  rw [← words_eq_block V e p]
  exact words_length _ _ _

end IndependentSetsGames.Foundations.Complexity.FinalCNFTemplate

end OAI
