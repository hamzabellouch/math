import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.BinPacking.Computation.MachineCanonicalOutput
import OAI.Computability.BinPacking.PCP.OccurrenceGame

namespace OAI

namespace BinPackingCompleteness.SourceClause

open BinPackingGames.Foundations.Target

abbrev Triple := Bool × Bool × Bool

def Triple.at (t : Triple) (i : Fin 3) : Bool :=
  match i.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

def literalTruth (positive value : Bool) : Bool :=
  if positive then value else !value

def localEval (signs values : Triple) : Bool :=
  (literalTruth signs.1 values.1 || literalTruth signs.2.1 values.2.1) ||
    literalTruth signs.2.2 values.2.2

def allTriples : List Triple :=
  [(false, false, false), (false, false, true),
   (false, true, false), (false, true, true),
   (true, false, false), (true, false, true),
   (true, true, false), (true, true, true)]

def satisfyingTriples (signs : Triple) : List Triple :=
  allTriples.filter (localEval signs)

theorem mem_allTriples (t : Triple) : t ∈ allTriples := by
  rcases t with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem mem_satisfyingTriples (signs values : Triple) :
    values ∈ satisfyingTriples signs ↔ localEval signs values = true := by
  simp [satisfyingTriples, mem_allTriples]

theorem satisfyingTriples_nodup (signs : Triple) :
    (satisfyingTriples signs).Nodup := by
  rcases signs with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem satisfyingTriples_length (signs : Triple) :
    (satisfyingTriples signs).length = 7 := by
  rcases signs with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

private theorem coordinate_truth_table :
    ∀ s₀ s₁ s₂ : Bool, ∀ i : Fin 3, ∀ value : Bool,
      ∃ a b c : Bool,
        localEval (s₀, s₁, s₂) (a, b, c) = true ∧
        Triple.at (a, b, c) i = value := by
  decide

theorem coordinate_surjective (signs : Triple) (i : Fin 3) (value : Bool) :
    ∃ t ∈ satisfyingTriples signs, t.at i = value := by
  obtain ⟨a, b, c, hs, hv⟩ :=
    coordinate_truth_table signs.1 signs.2.1 signs.2.2 i value
  exact ⟨(a, b, c), (mem_satisfyingTriples signs _).mpr hs, hv⟩

private theorem pair_truth_table :
    ∀ s₀ s₁ s₂ : Bool, ∀ i j : Fin 3, i ≠ j → ∀ first second : Bool,
      ∃ a b c : Bool,
        localEval (s₀, s₁, s₂) (a, b, c) = true ∧
        Triple.at (a, b, c) i = first ∧ Triple.at (a, b, c) j = second := by
  decide

theorem pair_surjective (signs : Triple) (i j : Fin 3) (distinct : i ≠ j)
    (first second : Bool) :
    ∃ t ∈ satisfyingTriples signs, t.at i = first ∧ t.at j = second := by
  obtain ⟨a, b, c, hs, hv⟩ :=
    pair_truth_table signs.1 signs.2.1 signs.2.2 i j distinct first second
  exact ⟨(a, b, c), (mem_satisfyingTriples signs _).mpr hs, hv⟩

structure NormalizedClause («variables» : Nat) where
  clause : Clause «variables»
  distinct : ∀ i j : Fin 3,
    clause[i].variableIndex = clause[j].variableIndex → i = j

def NormalizedClause.variable {n : Nat} (c : NormalizedClause n) (i : Fin 3) : Fin n :=
  c.clause[i].variableIndex

def NormalizedClause.signs {n : Nat} (c : NormalizedClause n) : Triple :=
  (c.clause[0].positive, c.clause[1].positive, c.clause[2].positive)

def NormalizedClause.restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) : Triple :=
  (assignment (c.variable 0), assignment (c.variable 1), assignment (c.variable 2))

@[simp] theorem localEval_restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) :
    localEval c.signs (c.restrict assignment) = c.clause.eval assignment := by
  rfl

theorem variable_ne {n : Nat} (c : NormalizedClause n) {i j : Fin 3}
    (different : i ≠ j) : c.variable i ≠ c.variable j :=
  fun same => different (c.distinct i j same)

def NormalizedClause.extend {n : Nat} (c : NormalizedClause n) (t : Triple) :
    Fin n → Bool :=
  fun v => if v = c.variable 0 then t.1 else if v = c.variable 1 then t.2.1 else t.2.2

@[simp] theorem restrict_extend {n : Nat} (c : NormalizedClause n) (t : Triple) :
    c.restrict (c.extend t) = t := by
  have h10 := variable_ne c (by decide : (1 : Fin 3) ≠ 0)
  have h20 := variable_ne c (by decide : (2 : Fin 3) ≠ 0)
  have h21 := variable_ne c (by decide : (2 : Fin 3) ≠ 1)
  simp [NormalizedClause.restrict, NormalizedClause.extend, h10, h20, h21]

theorem satisfying_label_realized {n : Nat} (c : NormalizedClause n) (t : Triple)
    (valid : t ∈ satisfyingTriples c.signs) :
    ∃ assignment : Fin n → Bool,
      c.restrict assignment = t ∧ c.clause.eval assignment = true := by
  refine ⟨c.extend t, restrict_extend c t, ?_⟩
  rw [← localEval_restrict, restrict_extend]
  exact (mem_satisfyingTriples c.signs t).mp valid

abbrev Occurrence (clauseCount : Nat) := Fin clauseCount × Fin 3

def occurrenceVariable {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) : Fin n :=
  (clauses e.1).variable e.2

theorem occurrence_determined_by_endpoints {n m : Nat}
    (clauses : Fin m → NormalizedClause n) (e e' : Occurrence m)
    (sameClause : e.1 = e'.1)
    (sameVariable : occurrenceVariable clauses e = occurrenceVariable clauses e') :
    e = e' := by
  rcases e with ⟨c, i⟩
  rcases e' with ⟨c', j⟩
  dsimp only at sameClause
  subst c'
  have samePosition : i = j := (clauses c).distinct i j sameVariable
  subst j
  rfl

theorem projection_determined_by_endpoints {n m : Nat}
    (clauses : Fin m → NormalizedClause n) (e e' : Occurrence m)
    (sameClause : e.1 = e'.1)
    (sameVariable : occurrenceVariable clauses e = occurrenceVariable clauses e')
    (label : Triple) : label.at e.2 = label.at e'.2 := by
  rw [occurrence_determined_by_endpoints clauses e e' sameClause sameVariable]

def agreementCount {n : Nat} (c : NormalizedClause n) (label : Triple)
    (assignment : Fin n → Bool) : Nat :=
  (if label.1 = assignment (c.variable 0) then 1 else 0) +
  (if label.2.1 = assignment (c.variable 1) then 1 else 0) +
  (if label.2.2 = assignment (c.variable 2) then 1 else 0)

theorem agreementCount_le_three {n : Nat} (c : NormalizedClause n) (label : Triple)
    (assignment : Fin n → Bool) : agreementCount c label assignment ≤ 3 := by
  unfold agreementCount
  split <;> split <;> split <;> omega

theorem agreementCount_le_two_of_unsatisfied {n : Nat}
    (c : NormalizedClause n) (label : Triple) (assignment : Fin n → Bool)
    (valid : localEval c.signs label = true)
    (unsatisfied : c.clause.eval assignment = false) :
    agreementCount c label assignment ≤ 2 := by
  by_cases h0 : label.1 = assignment (c.variable 0)
  · by_cases h1 : label.2.1 = assignment (c.variable 1)
    · by_cases h2 : label.2.2 = assignment (c.variable 2)
      · have same : label = c.restrict assignment :=
          Prod.ext h0 (Prod.ext h1 h2)
        rw [same, localEval_restrict, unsatisfied] at valid
        contradiction
      · simp [agreementCount, h0, h1, h2]
    · unfold agreementCount
      simp only [h0, h1, ↓reduceIte]
      split <;> omega
  · unfold agreementCount
    simp only [h0, ↓reduceIte]
    split <;> split <;> omega

theorem agreementCount_le_two_add_satisfied {n : Nat}
    (c : NormalizedClause n) (label : Triple) (assignment : Fin n → Bool)
    (valid : localEval c.signs label = true) :
    agreementCount c label assignment ≤
      2 + (if c.clause.eval assignment then 1 else 0) := by
  cases h : c.clause.eval assignment with
  | false => simpa [h] using agreementCount_le_two_of_unsatisfied c label assignment valid h
  | true => simpa [h] using agreementCount_le_three c label assignment

theorem totalAgreement_le {n : Nat} (states : List (NormalizedClause n × Triple))
    (assignment : Fin n → Bool)
    (valid : ∀ p ∈ states, localEval p.1.signs p.2 = true) :
    (states.map (fun p => agreementCount p.1 p.2 assignment)).sum ≤
      2 * states.length + (states.filter (fun p => p.1.clause.eval assignment)).length := by
  induction states with
  | nil => simp
  | cons p rest ih =>
      have hp := agreementCount_le_two_add_satisfied p.1 p.2 assignment
        (valid p (by simp))
      have hr := ih (fun p h => valid p (by simp [h]))
      cases h : p.1.clause.eval assignment <;>
        simp [h] at hp ⊢ <;> omega

end BinPackingCompleteness.SourceClause

namespace BinPackingCompleteness.Normalization

open BinPackingGames.Foundations
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

end BinPackingCompleteness.Normalization

namespace BinPackingCompleteness.NormalizationWords

open BinPackingGames.Foundations
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

end BinPackingCompleteness.NormalizationWords

namespace BinPackingCompleteness.SourceGame

open SourceClause BinPackingGames.Foundations.Games
open scoped BigOperators

def decodeLabel (signs : Triple) (label : Fin 7) : Triple :=
  (satisfyingTriples signs)[label.val]'(by
    rw [satisfyingTriples_length]
    exact label.isLt)

theorem decodeLabel_mem (signs : Triple) (label : Fin 7) :
    decodeLabel signs label ∈ satisfyingTriples signs := by
  exact List.getElem_mem _

theorem decodeLabel_legal (signs : Triple) (label : Fin 7) :
    localEval signs (decodeLabel signs label) = true :=
  (mem_satisfyingTriples signs _).mp (decodeLabel_mem signs label)

theorem decodeLabel_injective (signs : Triple) : Function.Injective (decodeLabel signs) := by
  intro a b same
  apply Fin.ext
  exact (List.Nodup.getElem_inj (satisfyingTriples_nodup signs)).mp same

def encodeLabel (signs label : Triple) (legal : localEval signs label = true) : Fin 7 :=
  ⟨(satisfyingTriples signs).idxOf label, by
    have h := List.idxOf_lt_length_of_mem ((mem_satisfyingTriples signs label).mpr legal)
    simpa using h⟩

@[simp] theorem decodeLabel_encodeLabel (signs label : Triple)
    (legal : localEval signs label = true) :
    decodeLabel signs (encodeLabel signs label legal) = label := by
  exact List.getElem_idxOf _

def projection {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) (answer : Fin 7) : Bool :=
  (decodeLabel (clauses e.1).signs answer).at e.2

theorem projection_surjective {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) (answer : Bool) :
    ∃ label : Fin 7, projection clauses e label = answer := by
  obtain ⟨t, legal, ht⟩ := coordinate_surjective (clauses e.1).signs e.2 answer
  refine ⟨encodeLabel (clauses e.1).signs t
    ((mem_satisfyingTriples _ _).mp legal), ?_⟩
  simpa [projection] using ht

theorem projection_pair_surjective {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (i j : Fin 3) (different : i ≠ j) (first second : Bool) :
    ∃ label : Fin 7,
      projection clauses (c, i) label = first ∧ projection clauses (c, j) label = second := by
  obtain ⟨t, legal, ht⟩ := pair_surjective (clauses c).signs i j different first second
  refine ⟨encodeLabel (clauses c).signs t ((mem_satisfyingTriples _ _).mp legal), ?_⟩
  simpa [projection] using ht

theorem leftAlphabet_card : Fintype.card (Fin 7) = 7 := by simp
theorem rightAlphabet_card : Fintype.card Bool = 2 := by decide

noncomputable section

def game {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) :
    OccurrenceGame (Occurrence m) (Fin m) (Fin n) (Fin 7) Bool :=
  OccurrenceGame.ofProjection (FiniteDistribution.uniform (Occurrence m))
    Prod.fst (occurrenceVariable clauses) (projection clauses)

theorem endpointDetermined {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) : (game clauses).EndpointDetermined := by
  intro e e' sameClause sameVariable a b
  have same := occurrence_determined_by_endpoints clauses e e' sameClause sameVariable
  subst e'
  rfl

def endpointPredicate {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (v : Fin n) (a : Fin 7) (b : Bool) : Bool :=
  decide (∃ i : Fin 3, (clauses c).variable i = v ∧
    (decodeLabel (clauses c).signs a).at i = b)

theorem endpointPredicate_eq_true {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (c : Fin m) (v : Fin n) (a : Fin 7) (b : Bool) :
    endpointPredicate clauses c v a b = true ↔
      ∃ i : Fin 3, (clauses c).variable i = v ∧
        (decodeLabel (clauses c).signs a).at i = b := by
  exact decide_eq_true_iff

def presentation {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) : (game clauses).EndpointPresentation where
  predicate := endpointPredicate clauses
  agrees e a b := by
    apply Bool.eq_iff_iff.mpr
    rw [endpointPredicate_eq_true]
    simp only [game, OccurrenceGame.ofProjection, occurrenceVariable, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨e.2, rfl, h⟩
    · rintro ⟨i, sameVariable, h⟩
      have samePosition : i = e.2 := (clauses e.1).distinct i e.2 sameVariable
      simpa [projection, samePosition] using h

def questionGame {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) :
    Game (Fin m) (Fin n) (Fin 7) Bool :=
  (game clauses).toGame (presentation clauses)

@[simp] theorem questionGame_success {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (questionGame clauses).success strategy = (game clauses).success strategy :=
  (game clauses).toGame_success (presentation clauses) strategy

theorem restrict_at {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) (i : Fin 3) :
    (c.restrict assignment).at i = assignment (c.variable i) := by
  have cases_three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases cases_three i with rfl | rfl | rfl <;> rfl

def completenessStrategy {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (assignment : Fin n → Bool) (satisfying : ∀ c, (clauses c).clause.eval assignment = true) :
    Strategy (Fin m) (Fin n) (Fin 7) Bool :=
  (fun c => encodeLabel (clauses c).signs ((clauses c).restrict assignment)
    (by simpa using satisfying c), assignment)

theorem completeness_wins {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) (e : Occurrence m) :
    (game clauses).wins (completenessStrategy clauses assignment satisfying) e = true := by
  simp only [game, OccurrenceGame.ofProjection, OccurrenceGame.wins, completenessStrategy,
    projection, decodeLabel_encodeLabel, decide_eq_true_eq]
  exact restrict_at (clauses e.1) assignment e.2

theorem completeness_success {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) :
    (game clauses).success (completenessStrategy clauses assignment satisfying) = 1 := by
  have h : (game clauses).wins (completenessStrategy clauses assignment satisfying) =
      fun _ => true := funext (completeness_wins clauses assignment satisfying)
  unfold OccurrenceGame.success
  rw [h, FiniteDistribution.probability_true]

theorem completeness_value {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (assignment : Fin n → Bool)
    (satisfying : ∀ c, (clauses c).clause.eval assignment = true) :
    (game clauses).value = 1 := by
  apply le_antisymm (game clauses).value_le_one
  rw [← completeness_success clauses assignment satisfying]
  exact (game clauses).success_le_value _

def winCount {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) : Nat :=
  ∑ c, agreementCount (clauses c) (decodeLabel (clauses c).signs (strategy.1 c)) strategy.2

def violatedCount {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (assignment : Fin n → Bool) : Nat :=
  ∑ c, if (clauses c).clause.eval assignment then 0 else 1

theorem winCount_add_violated_le {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    winCount clauses strategy + violatedCount clauses strategy.2 ≤ 3 * m := by
  unfold winCount violatedCount
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _c : Fin m, 3 := by
      apply Finset.sum_le_sum
      intro c _
      have h := agreementCount_le_two_add_satisfied (clauses c)
        (decodeLabel (clauses c).signs (strategy.1 c)) strategy.2
        (decodeLabel_legal _ _)
      cases heval : (clauses c).clause.eval strategy.2 <;>
        simp [heval] at h ⊢ <;> omega
    _ = 3 * m := by simp [Nat.mul_comm]

private theorem probability_uniform {E : Type*} [Fintype E] [Nonempty E]
    (event : E → Bool) :
    (FiniteDistribution.uniform E).probability event =
      (∑ e, if event e then (1 : ℝ) else 0) / (Fintype.card E : ℝ) := by
  unfold FiniteDistribution.probability FiniteDistribution.uniform
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  cases event e <;> simp

theorem success_eq_winCount_div {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (game clauses).success strategy = (winCount clauses strategy : ℝ) / (3 * (m : ℝ)) := by
  have hsum :
      (∑ e : Occurrence m, if (game clauses).wins strategy e then (1 : ℝ) else 0) =
        (winCount clauses strategy : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [winCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Fin.sum_univ_three]
    simp [game, OccurrenceGame.ofProjection, OccurrenceGame.wins, projection,
      occurrenceVariable, agreementCount, Triple.at, Nat.cast_add, Nat.cast_ite]
  change (FiniteDistribution.uniform (Occurrence m)).probability
    ((game clauses).wins strategy) = _
  rw [probability_uniform, hsum]
  congr 1
  simp [Occurrence, mul_comm]

theorem success_le_one_sub_third_violations {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n)
    (strategy : Strategy (Fin m) (Fin n) (Fin 7) Bool) :
    (game clauses).success strategy ≤
      1 - ((violatedCount clauses strategy.2 : ℝ) / (m : ℝ)) / 3 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
  have hden : (0 : ℝ) < 3 * (m : ℝ) := mul_pos (by norm_num) hm
  have hcount : (winCount clauses strategy : ℝ) +
      (violatedCount clauses strategy.2 : ℝ) ≤ 3 * (m : ℝ) := by
    exact_mod_cast winCount_add_violated_le clauses strategy
  rw [success_eq_winCount_div]
  apply (div_le_iff₀ hden).mpr
  have hidentity :
      (1 - ((violatedCount clauses strategy.2 : ℝ) / (m : ℝ)) / 3) * (3 * (m : ℝ)) =
        3 * (m : ℝ) - (violatedCount clauses strategy.2 : ℝ) := by
    field_simp [ne_of_gt hm]
  rw [hidentity]
  linarith

end
end BinPackingCompleteness.SourceGame

namespace BinPackingCompleteness.NormalizationEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution
open NormalizationWords

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Signs) × Option Bool

def clean (ambient : A) (signs : Signs) : State A := ((ambient, signs), none)

def sourceIndex : NameRef → Fin 6
  | .old i => ⟨i.val + 1, by have := i.isLt; omega⟩
  | .fresh _ => 0

theorem sourceIndex_ne_scratch (name : NameRef) : sourceIndex name ≠ 4 := by
  cases name with
  | old i =>
      intro h
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp only [sourceIndex] at hv
      omega
  | fresh i => simp [sourceIndex]

theorem sourceIndex_ne_output (name : NameRef) : sourceIndex name ≠ 5 := by
  cases name with
  | old i =>
      intro h
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp only [sourceIndex] at hv
      omega
  | fresh i => simp [sourceIndex]

inductive LocalLabel
  | copyOut
  | copyBack
  | emit
  deriving DecidableEq

protected abbrev LocalLabel.enumList : List LocalLabel := [.copyOut, .copyBack, .emit]

protected theorem LocalLabel.enumList_getElem?_ctorIdx_eq (x : LocalLabel) :
    LocalLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem LocalLabel.enumList_nodup : LocalLabel.enumList.Nodup := by decide

instance : Fintype LocalLabel where
  elems := ⟨LocalLabel.enumList, LocalLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def emitSign (output : K) (sign : SignRef) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => signValue state.1.2 sign)
    (.push output (fun _ => true)
      (.push output (fun _ => false) (exitAt output exit)))
    (.push output (fun _ => false) (exitAt output exit))

def emit (output : K) (literal : LiteralRecipe) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  pushWord output (List.replicate (offset literal.name) true ++ [false])
    (emitSign output literal.sign exit)

def localInstruction (tape : Fin 6 → K) (literal : LiteralRecipe)
    (labels : LocalLabel → Λ) (exit : Option Λ) :
    LocalLabel → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyOut => loopAt (tape (sourceIndex literal.name)) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape (sourceIndex literal.name))
      (tape 5) false (labels .copyBack) (some (labels .emit))
  | .emit => emit (tape 5) literal exit

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem stepAux_emit (output : K) (literal : LiteralRecipe) (exit : Option Λ)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat) :
    TM2.stepAux (emit output literal exit) (clean ambient signs)
      (Function.update base output
        (List.replicate (sourceValue names freshBase literal.name) true ++ base output)) =
      ⟨exit, clean ambient signs, Function.update base output
        ((literalBits signs names freshBase literal).reverse ++ base output)⟩ := by
  have nameOrder : nameValue names freshBase literal.name =
      offset literal.name + sourceValue names freshBase literal.name := by
    exact Nat.add_comm _ _
  have swapped : List.replicate (offset literal.name) true ++
      (List.replicate (sourceValue names freshBase literal.name) true ++ base output) =
      List.replicate (sourceValue names freshBase literal.name) true ++
        (List.replicate (offset literal.name) true ++ base output) := by
    calc
      _ = List.replicate
          (offset literal.name + sourceValue names freshBase literal.name) true ++ base output := by
            rw [List.replicate_add, List.append_assoc]
      _ = List.replicate
          (sourceValue names freshBase literal.name + offset literal.name) true ++ base output := by
            rw [Nat.add_comm (offset literal.name) (sourceValue names freshBase literal.name)]
      _ = _ := by rw [List.replicate_add, List.append_assoc]
  unfold emit
  rw [stepAux_pushWord]
  cases hs : signValue signs literal.sign <;> cases exit <;>
    simp [emitSign, clean, TM2.stepAux, exitAt, hs, literalBits,
      NormalizationWords.literalWords, encodeWords, encodeWord, nameOrder,
      List.reverse_append, List.reverse_replicate, List.replicate_add, List.append_assoc,
      -List.replicate_append_replicate] <;>
    rw [swapped]

theorem literalTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (literal : LiteralRecipe) (labels : LocalLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = localInstruction tape literal labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (sourceWord : base (tape (sourceIndex literal.name)) =
      List.replicate (sourceValue names freshBase literal.name) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[2 * (sourceValue names freshBase literal.name + 1) + 1]
      (some ⟨some (labels .copyOut), clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((literalBits signs names freshBase literal).reverse ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have copied := MachineCopy.copyTrace (tape (sourceIndex literal.name)) (tape 5) (tape 4)
    (hd _ _ (sourceIndex_ne_output _)) (hd _ _ (sourceIndex_ne_scratch _))
    (hd 5 4 (by decide)) false (labels .copyOut) (labels .copyBack)
    (some (labels .emit)) program (atLabels .copyOut) (atLabels .copyBack)
    base scratchEmpty (ambient, signs) none
  rw [sourceWord, List.length_replicate] at copied
  have emitted : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emit), clean ambient signs,
        Function.update base (tape 5)
          (List.replicate (sourceValue names freshBase literal.name) true ++ base (tape 5))⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((literalBits signs names freshBase literal).reverse ++ base (tape 5))⟩ := by
    change some (TM2.stepAux (program (labels .emit)) _ _) = _
    rw [atLabels .emit]
    exact congrArg some (stepAux_emit (tape 5) literal exit base ambient signs names freshBase)
  exact joinTrace copied emitted

def result (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) (output : List Bool) : List Bool :=
  (literalBits signs names freshBase literal).reverse ++ output

def cost (names : Names) (freshBase : Nat) (literal : LiteralRecipe) (_ : List Bool) : Nat :=
  2 * (sourceValue names freshBase literal.name + 1) + 1

def commandSteps (names : Names) (freshBase : Nat) (commands : List LiteralRecipe) : Nat :=
  (commands.map (fun literal => 2 * (sourceValue names freshBase literal.name + 1) + 1)).sum

theorem resultOf_eq (signs : Signs) (names : Names) (freshBase : Nat)
    (commands : List LiteralRecipe) (output : List Bool) :
    MachineFiniteSequence.resultOf (result signs names freshBase) commands output =
      (commands.flatMap (literalBits signs names freshBase)).reverse ++ output := by
  induction commands generalizing output with
  | nil => rfl
  | cons literal commands ih =>
      simp only [MachineFiniteSequence.resultOf, ih, result, List.flatMap_cons,
        List.reverse_append, List.append_assoc]

theorem sequenceSteps_eq (signs : Signs) (names : Names) (freshBase : Nat)
    (commands : List LiteralRecipe) (output : List Bool) :
    MachineFiniteSequence.steps (result signs names freshBase) (cost names freshBase)
      commands output = commandSteps names freshBase commands := by
  induction commands generalizing output with
  | nil => rfl
  | cons literal commands ih =>
      simp only [MachineFiniteSequence.steps, ih, commandSteps, List.map_cons,
        List.sum_cons, cost]

theorem sourceValue_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (name : NameRef) : sourceValue names freshBase name ≤ maximum := by
  cases name with
  | old i => exact nameBounds i
  | fresh i => exact freshBound

theorem commandSteps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (commands : List LiteralRecipe) :
    commandSteps names freshBase commands ≤ commands.length * (2 * maximum + 3) := by
  induction commands with
  | nil => simp [commandSteps]
  | cons literal commands ih =>
      have current := sourceValue_le names freshBase maximum freshBound nameBounds literal.name
      simp only [commandSteps, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

abbrev Labels (commands : List LiteralRecipe) :=
  MachineFiniteSequence.Label (fun _ : LiteralRecipe => LocalLabel) commands

def sequenceInstruction (tape : Fin 6 → K) (commands : List LiteralRecipe)
    (labels : Labels commands → Λ) (exit : Option Λ) :
    Labels commands → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  MachineFiniteSequence.instruction (fun _ => LocalLabel) (fun _ => LocalLabel.copyOut)
    (localInstruction tape) commands labels exit

def sequenceEntry (commands : List LiteralRecipe) (labels : Labels commands → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (fun _ => LocalLabel) (fun _ => LocalLabel.copyOut)
    commands labels exit

theorem sequenceTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (commands : List LiteralRecipe) (labels : Labels commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction tape commands labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (sourceWords : ∀ name, base (tape (sourceIndex name)) =
      List.replicate (sourceValue names freshBase name) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[commandSteps names freshBase commands]
      (some ⟨sequenceEntry commands labels exit, clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((commands.flatMap (literalBits signs names freshBase)).reverse ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have native := MachineFiniteSequence.trace (fun _ : LiteralRecipe => LocalLabel)
    (fun _ => LocalLabel.copyOut) (localInstruction tape)
    (result signs names freshBase) (cost names freshBase) program
    (fun _ => True) (fun _ => clean ambient signs)
    (fun output => Function.update base (tape 5) output) commands
    (fun _ _ _ _ => True.intro)
    (fun literal _ localLabels localExit localEquations output _ => by
      have actual := literalTrace tape distinct literal localLabels localExit program
        localEquations (Function.update base (tape 5) output) ambient signs names freshBase
        (by simp [hd (sourceIndex literal.name) 5 (sourceIndex_ne_output literal.name), sourceWords])
        (by simp [hd 4 5 (by decide), scratchEmpty])
      simpa only [cost, result, Function.update_self, Function.update_idem] using actual)
    labels exit atLabels (base (tape 5)) True.intro
  simpa only [sequenceSteps_eq, resultOf_eq, Function.update_eq_self,
    sequenceEntry] using native

abbrev Label := Labels recipe

def main : Label := .inl .copyOut

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  sequenceInstruction tape recipe labels exit

def steps (names : Names) (freshBase : Nat) : Nat := commandSteps names freshBase recipe

theorem steps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum) :
    steps names freshBase ≤ 39 * (2 * maximum + 3) := by
  simpa only [steps, recipe_length] using
    commandSteps_le names freshBase maximum freshBound nameBounds recipe

theorem gadgetTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (freshWord : base (tape 0) = List.replicate freshBase true)
    (oldWords : ∀ i, base (tape (sourceIndex (.old i))) = List.replicate (names i) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps names freshBase]
      (some ⟨some (labels main), clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((bits signs names freshBase).reverse ++ base (tape 5))⟩ := by
  have sources : ∀ name, base (tape (sourceIndex name)) =
      List.replicate (sourceValue names freshBase name) true := by
    intro name
    cases name with
    | old i => exact oldWords i
    | fresh i => exact freshWord
  have trace := sequenceTrace tape distinct recipe labels exit program atLabels
    base ambient signs names freshBase sources scratchEmpty
  have entry : sequenceEntry recipe labels exit = some (labels main) := rfl
  rw [← bits_eq_flatMap] at trace
  simpa only [steps, entry] using trace

def gadgetInTime (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names)
    (freshBase maximum : Nat)
    (freshWord : base (tape 0) = List.replicate freshBase true)
    (oldWords : ∀ i, base (tape (sourceIndex (.old i))) = List.replicate (names i) true)
    (scratchEmpty : base (tape 4) = [])
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), clean ambient signs, base⟩
      (some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((bits signs names freshBase).reverse ++ base (tape 5))⟩)
      (39 * (2 * maximum + 3)) where
  steps := steps names freshBase
  evals_in_steps := gadgetTrace tape distinct labels exit program atLabels base ambient
    signs names freshBase freshWord oldWords scratchEmpty
  steps_le_m := steps_le names freshBase maximum freshBound nameBounds

theorem label_finite : Finite Label := inferInstance

theorem state_finite [Finite A] : Finite (State A) := inferInstance

end BinPackingCompleteness.NormalizationEmitMachine

end OAI
