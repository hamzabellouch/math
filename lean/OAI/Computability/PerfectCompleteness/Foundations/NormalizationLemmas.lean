import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import OAI.Computability.PerfectCompleteness.Foundations.SourceClause
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.AlphabetTableBoundsLemmas

namespace OAI


namespace PerfectCompleteness.Normalization

open UniqueGamesTheorem.Foundations
open Target
open SourceClause

def tripleClause {n : Nat} (a b c : Fin n) (sa sb sc : Bool) : Clause n :=
  #v[⟨a, sa⟩, ⟨b, sb⟩, ⟨c, sc⟩]

def normalizedTriple {n : Nat} (a b c : Fin n) (sa sb sc : Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : NormalizedClause n where
  clause := tripleClause a b c sa sb sc
  distinct := by
    intro i j h
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi with rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl <;>
      simp_all [tripleClause]

def outputVariables (F : Formula) : Nat := F.variables + 4 * F.clauses.length

def oldVariable (F : Formula) (v : Fin F.variables) : Fin (outputVariables F) :=
  ⟨v.val, by have := v.isLt; unfold outputVariables; omega⟩

def freshVariable (F : Formula) (c : Fin F.clauses.length) (i : Fin 4) :
    Fin (outputVariables F) :=
  ⟨F.variables + 4 * c.val + i.val, by
    have hc := c.isLt
    have hi := i.isLt
    unfold outputVariables
    omega⟩

def copyVariable (F : Formula) (c : Fin F.clauses.length) (i : Fin 3) :
    Fin (outputVariables F) :=
  freshVariable F c ⟨i.val, by have := i.isLt; omega⟩

def paddingVariable (F : Formula) (c : Fin F.clauses.length) :
    Fin (outputVariables F) := freshVariable F c 3

theorem freshVariable_injective (F : Formula)
    (c d : Fin F.clauses.length) (i j : Fin 4)
    (h : freshVariable F c i = freshVariable F d j) : c = d ∧ i = j := by
  have hv := congrArg Fin.val h
  dsimp [freshVariable] at hv
  have hi := i.isLt
  have hj := j.isLt
  have hc : c.val = d.val := by omega
  have hij : i.val = j.val := by omega
  exact ⟨Fin.ext hc, Fin.ext hij⟩

theorem copy_ne_copy (F : Formula) (c : Fin F.clauses.length)
    {i j : Fin 3} (hij : i ≠ j) : copyVariable F c i ≠ copyVariable F c j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [copyVariable, freshVariable] at hv
  apply hij
  apply Fin.ext
  omega

theorem copy_ne_old (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) (v : Fin F.variables) : copyVariable F c i ≠ oldVariable F v := by
  intro h
  have hv := congrArg Fin.val h
  have hvlt := v.isLt
  dsimp [copyVariable, freshVariable, oldVariable] at hv
  omega

theorem copy_ne_padding (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) : copyVariable F c i ≠ paddingVariable F c := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  dsimp [copyVariable, paddingVariable, freshVariable] at hv
  omega

theorem old_ne_padding (F : Formula) (c : Fin F.clauses.length)
    (v : Fin F.variables) : oldVariable F v ≠ paddingVariable F c := by
  intro h
  have hv := congrArg Fin.val h
  have hvlt := v.isLt
  dsimp [paddingVariable, freshVariable, oldVariable] at hv
  omega

def mainClause (F : Formula) (c : Fin F.clauses.length) :
    NormalizedClause (outputVariables F) :=
  normalizedTriple (copyVariable F c 0) (copyVariable F c 1) (copyVariable F c 2)
    (PCP.clauseAt F c)[0].positive (PCP.clauseAt F c)[1].positive
    (PCP.clauseAt F c)[2].positive
    (copy_ne_copy F c (by decide)) (copy_ne_copy F c (by decide))
    (copy_ne_copy F c (by decide))

def equalityClauses (F : Formula) (c : Fin F.clauses.length) (i : Fin 3) :
    List (NormalizedClause (outputVariables F)) :=
  let x := copyVariable F c i
  let v := oldVariable F (PCP.clauseAt F c)[i].variableIndex
  let z := paddingVariable F c
  let hxv := copy_ne_old F c i (PCP.clauseAt F c)[i].variableIndex
  let hxz := copy_ne_padding F c i
  let hvz := old_ne_padding F c (PCP.clauseAt F c)[i].variableIndex
  [normalizedTriple x v z false true true hxv hxz hvz,
   normalizedTriple x v z false true false hxv hxz hvz,
   normalizedTriple x v z true false true hxv hxz hvz,
   normalizedTriple x v z true false false hxv hxz hvz]

def gadget (F : Formula) (c : Fin F.clauses.length) :
    List (NormalizedClause (outputVariables F)) :=
  [mainClause F c] ++ equalityClauses F c 0 ++
    equalityClauses F c 1 ++ equalityClauses F c 2

def gadgetClauses (F : Formula) (c : Fin F.clauses.length) :
    List (Clause (outputVariables F)) :=
  (gadget F c).map NormalizedClause.clause

@[simp] theorem equalityClauses_length (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) : (equalityClauses F c i).length = 4 := rfl

@[simp] theorem gadget_length (F : Formula) (c : Fin F.clauses.length) :
    (gadget F c).length = 13 := by simp [gadget]

@[simp] theorem gadgetClauses_length (F : Formula) (c : Fin F.clauses.length) :
    (gadgetClauses F c).length = 13 := by simp [gadgetClauses]

def restrictAssignment (F : Formula) (B : Fin (outputVariables F) → Bool) :
    Fin F.variables → Bool := fun v => B (oldVariable F v)

def extendAssignment (F : Formula) (A : Fin F.variables → Bool)
    (v : Fin (outputVariables F)) : Bool :=
  if old : v.val < F.variables then A ⟨v.val, old⟩
  else
    let c : Fin F.clauses.length := ⟨(v.val - F.variables) / 4, by
      have hv := v.isLt
      unfold outputVariables at hv
      omega⟩
    if slot : (v.val - F.variables) % 4 < 3 then
      A (PCP.clauseAt F c)[(⟨(v.val - F.variables) % 4, slot⟩ : Fin 3)].variableIndex
    else false

@[simp] theorem extend_oldVariable (F : Formula) (A : Fin F.variables → Bool)
    (v : Fin F.variables) : extendAssignment F A (oldVariable F v) = A v := by
  simp [extendAssignment, oldVariable, v.isLt]

@[simp] theorem extend_copyVariable (F : Formula) (A : Fin F.variables → Bool)
    (c : Fin F.clauses.length) (i : Fin 3) :
    extendAssignment F A (copyVariable F c i) = A (PCP.clauseAt F c)[i].variableIndex := by
  have hi := i.isLt
  have hold : ¬ F.variables + 4 * c.val + i.val < F.variables := by omega
  have hdiv : (F.variables + 4 * c.val + i.val - F.variables) / 4 = c.val := by omega
  have hmod : (F.variables + 4 * c.val + i.val - F.variables) % 4 = i.val := by omega
  simp [extendAssignment, copyVariable, freshVariable, hold, hdiv, hmod, hi]

@[simp] theorem restrict_extend (F : Formula) (A : Fin F.variables → Bool) :
    restrictAssignment F (extendAssignment F A) = A := by
  funext v
  exact extend_oldVariable F A v

theorem main_eval_of_copies_match (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool)
    (hcopy : ∀ i : Fin 3,
      B (copyVariable F c i) = B (oldVariable F (PCP.clauseAt F c)[i].variableIndex)) :
    (mainClause F c).clause.eval B = (PCP.clauseAt F c).eval (restrictAssignment F B) := by
  simp [mainClause, normalizedTriple, tripleClause, Clause.eval, Literal.eval,
    restrictAssignment, hcopy]

theorem equalityClauses_failures (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) (B : Fin (outputVariables F) → Bool) :
    PCP.VerifierToCNF.clauseFailures
      ((equalityClauses F c i).map NormalizedClause.clause) B =
      if B (copyVariable F c i) = B (oldVariable F (PCP.clauseAt F c)[i].variableIndex)
        then 0 else 1 := by
  cases hx : B (copyVariable F c i) <;>
    cases hv : B (oldVariable F (PCP.clauseAt F c)[i].variableIndex) <;>
    cases hz : B (paddingVariable F c) <;>
    simp only [Fin.getElem_fin] at hv <;>
    simp [PCP.VerifierToCNF.clauseFailures, equalityClauses, normalizedTriple,
      tripleClause, Clause.eval, Literal.eval, hx, hv, hz]

theorem gadget_failures (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool) :
    PCP.VerifierToCNF.clauseFailures (gadgetClauses F c) B =
      (if (mainClause F c).clause.eval B then 0 else 1) +
      (if B (copyVariable F c 0) = B (oldVariable F (PCP.clauseAt F c)[0].variableIndex)
        then 0 else 1) +
      (if B (copyVariable F c 1) = B (oldVariable F (PCP.clauseAt F c)[1].variableIndex)
        then 0 else 1) +
      (if B (copyVariable F c 2) = B (oldVariable F (PCP.clauseAt F c)[2].variableIndex)
        then 0 else 1) := by
  simp only [gadgetClauses, gadget, List.map_append,
    PCP.VerifierToCNF.clauseFailures_append, equalityClauses_failures]
  cases hmain : (mainClause F c).clause.eval B <;>
    simp [PCP.VerifierToCNF.clauseFailures, hmain]

theorem clauseFailures_zero_iff {n : Nat} (cs : List (Clause n)) (B : Fin n → Bool) :
    PCP.VerifierToCNF.clauseFailures cs B = 0 ↔ ∀ c ∈ cs, c.eval B = true := by
  rw [PCP.VerifierToCNF.clauseFailures, PCP.VerifierToCNF.zero_false_count_iff_all]
  simp only [List.all_map, Function.comp_def, id_eq, List.all_eq_true]

theorem gadget_complete_of_copies_match (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool)
    (hcopy : ∀ i : Fin 3,
      B (copyVariable F c i) = B (oldVariable F (PCP.clauseAt F c)[i].variableIndex))
    (hsat : (PCP.clauseAt F c).eval (restrictAssignment F B) = true) :
    ∀ d ∈ gadgetClauses F c, d.eval B = true := by
  apply (clauseFailures_zero_iff _ B).1
  rw [gadget_failures, main_eval_of_copies_match F c B hcopy, hsat]
  simp [hcopy]

theorem gadget_failure_domination (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool) :
    (if (PCP.clauseAt F c).eval (restrictAssignment F B) then 0 else 1) ≤
      PCP.VerifierToCNF.clauseFailures (gadgetClauses F c) B := by
  rw [gadget_failures]
  by_cases h0 : B (copyVariable F c 0) =
      B (oldVariable F (PCP.clauseAt F c)[0].variableIndex)
  · by_cases h1 : B (copyVariable F c 1) =
        B (oldVariable F (PCP.clauseAt F c)[1].variableIndex)
    · by_cases h2 : B (copyVariable F c 2) =
          B (oldVariable F (PCP.clauseAt F c)[2].variableIndex)
      · have hcopy : ∀ i : Fin 3,
            B (copyVariable F c i) =
              B (oldVariable F (PCP.clauseAt F c)[i].variableIndex) := by
          intro i
          have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi with rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h2
        rw [main_eval_of_copies_match F c B hcopy]
        simp [h0, h1, h2]
      · cases (PCP.clauseAt F c).eval (restrictAssignment F B) <;>
          simp [h0, h1, h2]
    · cases (PCP.clauseAt F c).eval (restrictAssignment F B) <;>
        simp [h0, h1]
      omega
  · cases (PCP.clauseAt F c).eval (restrictAssignment F B) <;>
      simp [h0]
    omega

theorem gadget_failed (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool)
    (unsatisfied : (PCP.clauseAt F c).eval (restrictAssignment F B) = false) :
    1 ≤ PCP.VerifierToCNF.clauseFailures (gadgetClauses F c) B := by
  simpa [unsatisfied] using gadget_failure_domination F c B

def normalizedClauses (F : Formula) : List (NormalizedClause (outputVariables F)) :=
  (PCP.allIndices F).flatMap (gadget F)

def normalize (F : Formula) : Formula where
  «variables» := outputVariables F
  clauses := (PCP.allIndices F).flatMap (gadgetClauses F)

theorem normalize_clauses_eq_map (F : Formula) :
    (normalize F).clauses = (normalizedClauses F).map NormalizedClause.clause := by
  simp only [normalize, normalizedClauses, List.map_flatMap]
  rfl

theorem normalize_distinct (F : Formula) (c : Clause (normalize F).variables)
    (hc : c ∈ (normalize F).clauses) (i j : Fin 3)
    (same : (c)[i].variableIndex = (c)[j].variableIndex) : i = j := by
  rw [normalize_clauses_eq_map] at hc
  obtain ⟨d, _, hd⟩ := List.mem_map.mp hc
  subst c
  exact d.distinct i j same

@[simp] theorem normalize_variables (F : Formula) :
    (normalize F).variables = F.variables + 4 * F.clauses.length := rfl

@[simp] theorem normalize_clause_count (F : Formula) :
    (normalize F).clauses.length = 13 * F.clauses.length := by
  change ((PCP.allIndices F).flatMap (gadgetClauses F)).length = _
  rw [PCP.VerifierToCNF.length_flatMap_constant _ _ 13
    (fun c _ => gadgetClauses_length F c)]
  simp [PCP.allIndices, Nat.mul_comm]

theorem normalize_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    (normalize F).clauses ≠ [] := by
  have hm : 0 < F.clauses.length := List.length_pos_iff.mpr hne
  have hout : 0 < (normalize F).clauses.length := by
    rw [normalize_clause_count]
    omega
  exact List.ne_nil_of_length_pos hout

theorem normalize_completeness (F : Formula) (hs : F.Satisfiable) :
    (normalize F).Satisfiable := by
  obtain ⟨A, hA⟩ := hs
  refine ⟨extendAssignment F A, ?_⟩
  intro d hd
  obtain ⟨c, _, hd⟩ := List.mem_flatMap.mp hd
  apply gadget_complete_of_copies_match F c (extendAssignment F A) ?_ ?_ d hd
  · intro i
    simp
  · rw [restrict_extend]
    exact hA _ (List.getElem_mem c.isLt)

theorem failedCount_domination (F : Formula) (B : Fin (normalize F).variables → Bool) :
    PCP.NameCompaction.failedCount F (restrictAssignment F B) ≤
      PCP.NameCompaction.failedCount (normalize F) B := by
  change Fin (outputVariables F) → Bool at B
  change (PCP.NameCompaction.evaluationList F (restrictAssignment F B)).count false ≤
    PCP.VerifierToCNF.clauseFailures ((PCP.allIndices F).flatMap (gadgetClauses F)) B
  rw [← PCP.NameCompaction.evaluations_allIndices F (restrictAssignment F B),
    PCP.VerifierToCNF.count_false_map_sum, PCP.VerifierToCNF.clauseFailures_flatMap]
  exact PCP.VerifierToCNF.nat_sum_map_le _ _ _
    (fun c _ => gadget_failure_domination F c B)

theorem normalize_reflects (F : Formula) (hs : (normalize F).Satisfiable) :
    F.Satisfiable := by
  obtain ⟨B, hB⟩ := hs
  have hout : PCP.NameCompaction.failedCount (normalize F) B = 0 :=
    (clauseFailures_zero_iff (normalize F).clauses B).2 hB
  have hin : PCP.NameCompaction.failedCount F (restrictAssignment F B) = 0 := by
    have h := failedCount_domination F B
    rw [hout] at h
    omega
  exact ⟨restrictAssignment F B, (clauseFailures_zero_iff F.clauses _).1 hin⟩

theorem normalize_satisfiable_iff (F : Formula) :
    (normalize F).Satisfiable ↔ F.Satisfiable :=
  ⟨normalize_reflects F, normalize_completeness F⟩

theorem normalize_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * PCP.NameCompaction.failedCount F A)
    (B : Fin (normalize F).variables → Bool) :
    a * (normalize F).clauses.length ≤
      (13 * b) * PCP.NameCompaction.failedCount (normalize F) B := by
  have hsource := gap (restrictAssignment F B)
  have hcount := Nat.mul_le_mul_left b (failedCount_domination F B)
  rw [normalize_clause_count]
  calc
    a * (13 * F.clauses.length) = 13 * (a * F.clauses.length) := by ac_rfl
    _ ≤ 13 * (b * PCP.NameCompaction.failedCount (normalize F) B) :=
      Nat.mul_le_mul_left 13 (hsource.trans hcount)
    _ = (13 * b) * PCP.NameCompaction.failedCount (normalize F) B := by ac_rfl

end PerfectCompleteness.Normalization



namespace PerfectCompleteness.NormalizationWords


open UniqueGamesTheorem.Foundations
open Complexity

abbrev Signs := Fin 3 → Bool
abbrev Names := Fin 3 → Nat

inductive NameRef
  | old (slot : Fin 3)
  | fresh (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive SignRef
  | source (slot : Fin 3)
  | constant (sign : Bool)
  deriving DecidableEq, Fintype

structure LiteralRecipe where
  name : NameRef
  sign : SignRef
  deriving DecidableEq, Fintype

def sourceValue (names : Names) (freshBase : Nat) : NameRef → Nat
  | .old i => names i
  | .fresh _ => freshBase

def offset : NameRef → Nat
  | .old _ => 0
  | .fresh i => i.val

def nameValue (names : Names) (freshBase : Nat) (name : NameRef) : Nat :=
  sourceValue names freshBase name + offset name

def signValue (signs : Signs) : SignRef → Bool
  | .source i => signs i
  | .constant sign => sign

def literalWords (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) : List Nat :=
  [nameValue names freshBase literal.name, if signValue signs literal.sign then 1 else 0]

def literalBits (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) : List Bool :=
  encodeWords (literalWords signs names freshBase literal)

def mainRecipe : List LiteralRecipe :=
  [⟨.fresh 0, .source 0⟩, ⟨.fresh 1, .source 1⟩, ⟨.fresh 2, .source 2⟩]

def equalityRecipe (i : Fin 3) : List LiteralRecipe :=
  [⟨.fresh i.castSucc, .constant false⟩, ⟨.old i, .constant true⟩, ⟨.fresh 3, .constant true⟩,
   ⟨.fresh i.castSucc, .constant false⟩, ⟨.old i, .constant true⟩, ⟨.fresh 3, .constant false⟩,
   ⟨.fresh i.castSucc, .constant true⟩, ⟨.old i, .constant false⟩, ⟨.fresh 3, .constant true⟩,
   ⟨.fresh i.castSucc, .constant true⟩, ⟨.old i, .constant false⟩, ⟨.fresh 3, .constant false⟩]

def recipe : List LiteralRecipe :=
  mainRecipe ++ equalityRecipe 0 ++ equalityRecipe 1 ++ equalityRecipe 2

@[simp] theorem recipe_length : recipe.length = 39 := by decide

def words (signs : Signs) (names : Names) (freshBase : Nat) : List Nat :=
  recipe.flatMap (literalWords signs names freshBase)

def bits (signs : Signs) (names : Names) (freshBase : Nat) : List Bool :=
  encodeWords (words signs names freshBase)

def clauseSigns {n : Nat} (clause : Target.Clause n) : Signs := fun i => clause[i].positive

def clauseNames {n : Nat} (clause : Target.Clause n) : Names := fun i => clause[i].variableIndex.val

theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem bits_eq_flatMap (signs : Signs) (names : Names) (freshBase : Nat) :
    bits signs names freshBase = recipe.flatMap (literalBits signs names freshBase) :=
  encodeWords_flatMap _ _

theorem gadget_words (formula : Target.Formula) (c : Fin formula.clauses.length) :
    (Normalization.gadgetClauses formula c).flatMap Complexity.clauseWords =
      words (clauseSigns (PCP.clauseAt formula c)) (clauseNames (PCP.clauseAt formula c))
        (formula.variables + 4 * c.val) := by
  simp [Normalization.gadgetClauses, Normalization.gadget, Normalization.mainClause,
    Normalization.equalityClauses, Normalization.normalizedTriple, Normalization.tripleClause,
    Normalization.copyVariable, Normalization.freshVariable, Normalization.oldVariable,
    Normalization.paddingVariable, Complexity.clauseWords, Complexity.literalWords,
    words, recipe, mainRecipe, equalityRecipe, literalWords, nameValue, sourceValue, offset,
    signValue, clauseSigns, clauseNames, Fin.getElem_fin]
  exact ⟨rfl, rfl, rfl⟩

theorem gadget_bits (formula : Target.Formula) (c : Fin formula.clauses.length) :
    encodeWords ((Normalization.gadgetClauses formula c).flatMap Complexity.clauseWords) =
      bits (clauseSigns (PCP.clauseAt formula c)) (clauseNames (PCP.clauseAt formula c))
        (formula.variables + 4 * c.val) := by
  rw [gadget_words]
  rfl

def body (formula : Target.Formula) : List Bool :=
  (PCP.allIndices formula).flatMap (fun c =>
    bits (clauseSigns (PCP.clauseAt formula c)) (clauseNames (PCP.clauseAt formula c))
      (formula.variables + 4 * c.val))

theorem encoded_body (formula : Target.Formula) :
    encodeWords ((Normalization.normalize formula).clauses.flatMap Complexity.clauseWords) =
      body formula := by
  change encodeWords (((PCP.allIndices formula).flatMap
    (Normalization.gadgetClauses formula)).flatMap Complexity.clauseWords) = _
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [gadget_bits, body]

theorem encoded_normalize (formula : Target.Formula) :
    formulaBits (Normalization.normalize formula) =
      encodeWord (formula.variables + 4 * formula.clauses.length) ++
        encodeWord (13 * formula.clauses.length) ++ body formula := by
  have count : (Normalization.normalize formula).clauses.length =
      13 * formula.clauses.length := Normalization.normalize_clause_count formula
  simp only [formulaBits, formulaWords, encodeWords_append, encodeWords, List.append_nil,
    Normalization.normalize_variables, List.append_assoc]
  erw [count, encoded_body]

end PerfectCompleteness.NormalizationWords



namespace PerfectCompleteness.NormalizationStream

open UniqueGamesTheorem.Foundations Complexity NormalizationWords

def blocks {n : Nat} (freshBase : Nat) : List (Target.Clause n) → List Bool
  | [] => []
  | clause :: clauses =>
      bits (clauseSigns clause) (clauseNames clause) freshBase ++ blocks (freshBase + 4) clauses

theorem blocks_eq_finRange {n : Nat} (clauses : List (Target.Clause n)) (freshBase : Nat) :
    blocks freshBase clauses = (List.finRange clauses.length).flatMap (fun i =>
      bits (clauseSigns clauses[i.val]) (clauseNames clauses[i.val]) (freshBase + 4 * i.val)) := by
  induction clauses generalizing freshBase with
  | nil => simp [blocks]
  | cons clause clauses ih =>
      simp only [blocks, List.length_cons, List.finRange_succ, List.flatMap_cons,
        List.flatMap_map, List.getElem_cons_zero, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
      apply congrArg (fun tail => bits (clauseSigns clause) (clauseNames clause) freshBase ++ tail)
      rw [ih]
      apply List.flatMap_congr
      intro i _
      have address : freshBase + 4 + 4 * i.val = freshBase + 4 * (i.val + 1) := by omega
      simp only [Fin.val_succ, List.getElem_cons_succ, address]

theorem body_eq_blocks (formula : Target.Formula) :
    NormalizationWords.body formula = blocks formula.variables formula.clauses := by
  rw [blocks_eq_finRange]
  rfl

theorem encoded_normalize (formula : Target.Formula) :
    formulaBits (Normalization.normalize formula) =
      encodeWord (formula.variables + 4 * formula.clauses.length) ++
        encodeWord (13 * formula.clauses.length) ++ blocks formula.variables formula.clauses := by
  rw [NormalizationWords.encoded_normalize, body_eq_blocks]

theorem blocks_length_le {n : Nat} (clauses : List (Target.Clause n)) (freshBase : Nat)
    (bound : Nat) (oldBound : n ≤ bound) (freshBound : freshBase + 4 * clauses.length ≤ bound) :
    (blocks freshBase clauses).length ≤ clauses.length * (39 * (bound + 3)) := by
  have literalBound (names : Names) (fresh : Nat) (signs : Signs)
      (hn : ∀ i, names i ≤ bound) (hf : fresh + 3 ≤ bound) (literal : LiteralRecipe) :
      (literalBits signs names fresh literal).length ≤ bound + 3 := by
    have nameBound : nameValue names fresh literal.name ≤ bound := by
      cases h : literal.name with
      | old i => simpa [nameValue, sourceValue, offset, h] using hn i
      | fresh i =>
          have hi := i.isLt
          simp only [nameValue, sourceValue, offset]
          omega
    cases h : signValue signs literal.sign <;>
      simp [literalBits, NormalizationWords.literalWords, h] <;> omega
  have gadgetBound (clause : Target.Clause n) (fresh : Nat) (hf : fresh + 3 ≤ bound) :
      (bits (clauseSigns clause) (clauseNames clause) fresh).length ≤ 39 * (bound + 3) := by
    rw [bits_eq_flatMap]
    have listBound (commands : List LiteralRecipe) :
        (commands.flatMap (literalBits (clauseSigns clause) (clauseNames clause) fresh)).length ≤
          commands.length * (bound + 3) := by
      induction commands with
      | nil => simp
      | cons command commands ih =>
          have hc := literalBound (clauseNames clause) fresh (clauseSigns clause)
            (fun i => Nat.le_trans (clause[i].variableIndex.isLt.le) oldBound) hf command
          simp only [List.flatMap_cons, List.length_append, List.length_cons,
            Nat.add_mul, Nat.one_mul]
          omega
    simpa only [recipe_length] using listBound recipe
  induction clauses generalizing freshBase with
  | nil => simp [blocks]
  | cons clause clauses ih =>
      have head := gadgetBound clause freshBase (by simp only [List.length_cons] at freshBound; omega)
      have tail := ih (freshBase + 4) (by simp only [List.length_cons] at freshBound; omega)
      simp only [blocks, List.length_append, List.length_cons]
      nlinarith

end PerfectCompleteness.NormalizationStream

end OAI
