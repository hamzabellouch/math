import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.FinalCNFPattern
import OAI.Combinatorics.IndependentSets.Machines.AmbientRelation
import OAI.Combinatorics.IndependentSets.PCP.FinalCNFTemplate

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]
    norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
