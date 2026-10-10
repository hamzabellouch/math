import Mathlib
import OAI.Computability.MinUncut.PCP.FinalBooleanVerifier

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv

theorem labelEquiv_val (label : Label) :
    (labelEquiv label).val =
      ∑ i : Fin 6, AlphabetTable.Enumeration.bitValue (label i) * 2 ^ i.val :=
  AlphabetTable.Enumeration.labelEquiv_val label

def labelIndex (label : Label) : Fin 64 := labelEquiv label

def labelBits (index : Fin 64) : Label := labelEquiv.symm index

@[simp] theorem labelBits_labelIndex (label : Label) :
    labelBits (labelIndex label) = label := labelEquiv.symm_apply_apply label

@[simp] theorem labelIndex_labelBits (index : Fin 64) :
    labelIndex (labelBits index) = index := labelEquiv.apply_symm_apply index

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

def relationAddress (bits : VerifierToCNF.Pattern 12) : Fin 4096 :=
  GraphTables.relationIndex (labelIndex (leftHalf bits), labelIndex (rightHalf bits))

theorem relationAddress_val (bits : VerifierToCNF.Pattern 12) :
    (relationAddress bits).val =
      64 * (labelIndex (leftHalf bits)).val + (labelIndex (rightHalf bits)).val := by
  rw [relationAddress, GraphTables.relationIndex_val, Nat.add_comm]

def patternRelationIndex (p : VerifierToCNF.PatternIndex 12) : Fin 4096 :=
  relationAddress (VerifierToCNF.patternAt 12 p)

@[simp] theorem patternRelationIndex_eq (p : VerifierToCNF.PatternIndex 12) :
    patternRelationIndex p = relationAddress (VerifierToCNF.patternAt 12 p) := rfl

def tableGraph (table : GraphTables.Table) :
    ConstraintGraph (Fin table.vertices) (Fin table.darts) Label :=
  (GraphTables.semantics table).reindex (Equiv.refl _) (Equiv.refl _) labelEquiv.symm

@[simp] theorem tableGraph_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).tail e = table.rows[e].tail := rfl

@[simp] theorem tableGraph_reverse (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem tableGraph_accepts (table : GraphTables.Table) (e : Fin table.darts)
    (a b : Label) :
    (tableGraph table).accepts e a b =
      GraphTables.relationAt table.rows[e].relation (labelIndex a) (labelIndex b) := rfl

abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem relation_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (bits : VerifierToCNF.Pattern 12) :
    table.rows[e].relation[relationAddress bits] =
      (tableVerifier table).accepts e bits := rfl

theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl

theorem verifier_accepts_eq_lookup (table : GraphTables.Table)
    (e : Fin table.darts) (bits : VerifierToCNF.Pattern 12) :
    (tableVerifier table).accepts e bits =
      table.rows[e].relation[relationAddress bits] := rfl

theorem buffer_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (buffer : Fin 4096 → Bool)
    (read_correct : ∀ i, buffer i = table.rows[e].relation[i])
    (bits : VerifierToCNF.Pattern 12) :
    buffer (relationAddress bits) = (tableVerifier table).accepts e bits :=
  (read_correct _).trans (relation_lookup_eq_verifier_accepts table e bits)

theorem pattern_buffer_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (buffer : Fin 4096 → Bool)
    (read_correct : ∀ i, buffer i = table.rows[e].relation[i])
    (p : VerifierToCNF.PatternIndex 12) :
    buffer (patternRelationIndex p) =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) :=
  buffer_lookup_eq_verifier_accepts table e buffer read_correct _

end MinUncutGames.Foundations.Complexity.FinalCNFPattern

end

end OAI
