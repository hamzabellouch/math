import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.Contexts
import OAI.Combinatorics.IndependentSets.Machines.Tape
import OAI.Combinatorics.IndependentSets.Encoding.Encoding
import OAI.Combinatorics.IndependentSets.Fourier.LocalEquations

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceOccurrences
open IndependentSetsGames.Reduction.CloneGap
open scoped BigOperators

open SourceContexts
open IndependentSetsGames.Reduction.FiniteNoise

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def slotEncoding : Encoding PCP.Slot where
  size := 3
  code :=
    { toFun := fun s => match s with | .first => 0 | .second => 1 | .third => 2
      invFun := fun i => if i.val = 0 then .first else if i.val = 1 then .second else .third
      left_inv := by intro s; cases s <;> rfl
      right_inv := by decide }

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.«variables»)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)
def slotContextEncoding (u : ℕ) : Encoding (SlotContext u) :=
  (Encoding.fin u).function slotEncoding

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.«variables» ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def dummyIndex (F : Target.Formula) (u : ℕ) : Fin (nBits F u) :=
  (proofEncoding F u).code (.inr (.inr ()))

def leftAnchor (u : ℕ) : I u := fun _ => false

def rightAnchor (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    Option {j : J u // validJ F c j = true} := firstValid (jEncoding u) (validJ F c)

theorem rightAnchor_none_iff (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    rightAnchor F c = none ↔ ∀ j : J u, validJ F c j = false :=
  firstValid_none_iff _ _

def halfTableKeyAssignment (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) :
    GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u) → Bool
  | .inl (v, f) => a v (canonicalInput (leftAnchor u) f)
  | .inr (.inl (c, g)) =>
    match rightAnchor F c with
    | none => false
    | some j₀ => b c j₀ (canonicalInput j₀ (restrictQuery (validJ F c) g))
  | .inr (.inr _) => false

def extendHalfTables (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)
    (halfTableKeyAssignment F u a b)

@[simp] theorem extendHalfTables_left (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) (v : VariableContext F u) (h : HalfCube (leftAnchor u)) :
    extendHalfTables F u a b ((proofEncoding F u).code (.inl (v, h.val))) = a v h := by
  calc
    _ = halfTableKeyAssignment F u a b (.inl (v, h.val)) :=
      assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
        (jEncoding u) (halfTableKeyAssignment F u a b) (.inl (v, h.val))
    _ = a v h := congrArg (a v) (canonicalInput_half (leftAnchor u) h)

theorem extendHalfTables_right (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) (c : ClauseContext F u)
    (j₀ : {j : J u // validJ F c j = true}) (hanchor : rightAnchor F c = some j₀)
    (h : HalfCube j₀) :
    extendHalfTables F u a b ((proofEncoding F u).code
      (.inr (.inl (c, extendRestricted (validJ F c) h.val)))) = b c j₀ h := by
  calc
    _ = halfTableKeyAssignment F u a b
        (.inr (.inl (c, extendRestricted (validJ F c) h.val))) :=
      assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
        (jEncoding u) (halfTableKeyAssignment F u a b) _
    _ = b c j₀ h := by
      simp only [halfTableKeyAssignment, hanchor]
      rw [restrictQuery_extendRestricted, canonicalInput_half]

def emptyAddress (F : Target.Formula) (u : ℕ) (v : VariableContext F u) :
    EmptyContext.Address (leftAnchor u) → Fin (nBits F u)
  | .inl h => (proofEncoding F u).code (.inl (v, h.val))
  | .inr _ => dummyIndex F u

def contextEquation (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (Fin (nBits F u)) :=
  match rightAnchor F c with
  | none => mapEquation (emptyAddress F u v) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => conditionedOccurrence (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      t.1 t.2.2 (realizedNoise t.2.1)

def leftResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : Cube (I u) → Bool :=
  foldedAnswer (leftAnchor u) (fun h => bits ((proofEncoding F u).code (.inl (v, h.val))))

def rightResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : Cube (J u) → Bool :=
  match rightAnchor F c with
  | none => fun _ => false
  | some j₀ => conditionedFoldedAnswer (validJ F c) j₀
      (fun h => bits ((proofEncoding F u).code (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

theorem contextEquation_satisfied (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) (bits : Fin (nBits F u) → Bool) :
    satisfied (contextEquation F u D c v t) bits =
      !(leftResponse F u bits v t.1 ^^ rightResponse F u bits c t.2.2 ^^
        rightResponse F u bits c (thirdQuery (pi F c v) t.1 t.2.2 (realizedNoise t.2.1))) := by
  cases ha : rightAnchor F c with
  | none =>
    simp only [contextEquation, ha, satisfied_mapEquation, EmptyContext.equation_satisfied,
      rightResponse, Bool.xor_false]
    rfl
  | some j₀ =>
    simp only [contextEquation, ha, rightResponse]
    exact conditionedOccurrence_satisfied (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      bits t.1 t.2.2 (realizedNoise t.2.1)

def testTapeEncoding (u D : ℕ) : Encoding (SourceTape.TestTape (I u) (J u) D) :=
  ((iEncoding u).function Encoding.bool).prod
    (((jEncoding u).function (Encoding.fin D)).prod ((jEncoding u).function Encoding.bool))

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

def sourceIndexEncoding (F : Target.Formula) (u D : ℕ) : Encoding (SourceIndex F u D) :=
  ((clauseEncoding F u).prod (slotContextEncoding u)).prod (testTapeEncoding u D)

def sourceEquation (F : Target.Formula) (u D : ℕ) (p : SourceIndex F u D) :
    Equation (Fin (nBits F u)) :=
  contextEquation F u D p.1.1 (sampledVariables F p.1.1 p.1.2) p.2

def rawSourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  occurrenceList (sourceIndexEncoding F u D) (sourceEquation F u D)

@[simp] theorem rawSourceList_length (F : Target.Formula) (u D : ℕ) :
    (rawSourceList F u D).length =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [rawSourceList, occurrenceList_length]
  rfl

theorem rawSourceList_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (bits : Fin (nBits F u) → Bool) :
    ((rawSourceList F u D).countP (fun e => satisfied e bits) : ℝ) /
        (rawSourceList F u D).length =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
          (leftResponse F u bits (sampledVariables F c s)) (rightResponse F u bits c) := by
  rw [rawSourceList, occurrenceList_acceptance, SourceTape.expect_prod]
  rw [SourceTape.expect_prod]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro s _
  rw [← SourceTape.tapeAcceptance_eq_testAcceptance hD]
  unfold SourceTape.tapeAcceptance
  apply Finset.expect_congr rfl
  intro t _
  rw [sourceEquation, contextEquation_satisfied]
  cases h : leftResponse F u bits (sampledVariables F c s) t.1 ^^
    rightResponse F u bits c t.2.2 ^^
      rightResponse F u bits c
        (thirdQuery (pi F c (sampledVariables F c s)) t.1 t.2.2 (realizedNoise t.2.1)) <;> rfl

def emptyFormulaEquation (F : Target.Formula) (u : ℕ) : Equation (Fin (nBits F u)) :=
  ⟨dummyIndex F u, dummyIndex F u, dummyIndex F u, false⟩

def sourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  if F.clauses.isEmpty then [emptyFormulaEquation F u] else rawSourceList F u D

theorem sourceList_empty (F : Target.Formula) (u D : ℕ) (h : F.clauses = []) :
    sourceList F u D = [emptyFormulaEquation F u] := by simp [sourceList, h]

theorem sourceList_nonempty (F : Target.Formula) (u D : ℕ) (h : F.clauses ≠ []) :
    sourceList F u D = rawSourceList F u D := by
  unfold sourceList
  rw [List.isEmpty_eq_false_iff.mpr h]
  rfl

theorem sourceList_length_le_raw_add_one (F : Target.Formula) (u D : ℕ) :
    (sourceList F u D).length ≤ (rawSourceList F u D).length + 1 := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    rw [List.length_singleton]
    omega
  · rw [sourceList_nonempty F u D h]
    omega

theorem sourceList_ne_nil (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    sourceList F u D ≠ [] := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    simp
  · rw [sourceList_nonempty F u D h]
    apply List.length_pos_iff.mp
    rw [rawSourceList_length]
    have hc : 0 < F.clauses.length := List.length_pos_iff.mpr h
    positivity

def sourceInput (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    IndependentSetsGames.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩

theorem emptyFormulaEquation_satisfied (F : Target.Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) :
    satisfied (emptyFormulaEquation F u) bits = !(bits (dummyIndex F u)) := by
  cases h : bits (dummyIndex F u) <;> simp [emptyFormulaEquation, satisfied, h]

end IndependentSetsGames.Foundations.Hastad.SourceOccurrences

end OAI
