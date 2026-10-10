import Mathlib
import OAI.Computability.MaxCut.PCP.HonestTest
import OAI.Computability.MaxCut.Encoding.Encoding2

namespace OAI

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace MaxCutGames.Foundations.Hastad.SourceOccurrences

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

/-- A concrete, reversible finite encoding. Constructors below specify the
actual arithmetic; no arbitrary `Fintype.equivFin` is used. -/
structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

/-- The second component is the low-order block coordinate. -/
def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

/-- The right summand follows the whole left block. -/
def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

/-- Function coordinate zero is the least significant radix digit. -/
def function {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α → β) where
  size := b.size ^ a.size
  code := (show (α → β) ≃ (Fin a.size → Fin b.size) from
    { toFun := fun f i => b.code (f (a.code.symm i))
      invFun := fun f x => b.code.symm (f (a.code x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro f; funext i; simp }).trans finFunctionFinEquiv

def enumerate {α : Type} (a : Encoding α) : List α := List.ofFn a.code.symm

@[simp] theorem length_enumerate {α : Type} (a : Encoding α) :
    a.enumerate.length = a.size := by simp [enumerate]

theorem mem_enumerate {α : Type} (a : Encoding α) (x : α) : x ∈ a.enumerate := by
  rw [enumerate, List.mem_ofFn']
  exact ⟨a.code x, a.code.symm_apply_apply x⟩

theorem nodup_enumerate {α : Type} (a : Encoding α) : a.enumerate.Nodup :=
  List.nodup_ofFn_ofInjective a.code.symm.injective

theorem card_eq_size {α : Type} [Fintype α] (a : Encoding α) :
    Fintype.card α = a.size := by
  simpa only [Fintype.card_fin] using Fintype.card_congr a.code

end Encoding

/-- Distinct table vertices and the three side tags never share storage.
Unused ambient query positions are harmless explicit padding. -/
abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((c.prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v c i j).size =
      v.size * 2 ^ i.size + (c.size * 2 ^ j.size + 1) := rfl

/-- Extending by false gives a unique padded address to a restricted query. -/
def extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) : Cube J :=
  fun j => if h : valid j = true then f ⟨j, h⟩ else false

@[simp] theorem extendRestricted_valid {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) (j : {j : J // valid j = true}) :
    extendRestricted valid f j.val = f j := by simp [extendRestricted, j.property]

theorem extendRestricted_injective {J : Type} (valid : J → Bool) :
    Function.Injective (extendRestricted valid) := by
  intro f g h
  funext j
  have := congrFun h j.val
  simpa only [extendRestricted_valid] using this

@[simp] theorem restrictQuery_extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) :
    restrictQuery valid (extendRestricted valid f) = f := by
  funext j
  exact extendRestricted_valid valid f j

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

/-- The global index map is an explicit equivalence, including all padding. -/
def assignmentOfKey {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) : Fin (globalEncoding v c i j).size → Bool :=
  fun q => bits ((globalEncoding v c i j).code.symm q)

@[simp] theorem assignmentOfKey_code {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) (key : GlobalKey V C I J) :
    assignmentOfKey v c i j bits ((globalEncoding v c i j).code key) = bits key := by
  exact congrArg bits ((globalEncoding v c i j).code.symm_apply_apply key)

theorem assignmentOfKey_surjective {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Function.Surjective (assignmentOfKey v c i j) := by
  intro bits
  refine ⟨fun key => bits ((globalEncoding v c i j).code key), ?_⟩
  funext q
  exact congrArg bits ((globalEncoding v c i j).code.apply_symm_apply q)

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def localAddress (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    FoldedEquation.Address i₀ j₀ → Fin (globalEncoding vE cE iE jE).size
  | .inl f => (globalEncoding vE cE iE jE).code (.inl (v, f.val))
  | .inr g => (globalEncoding vE cE iE jE).code (.inr (.inl (c, extendRestricted valid g.val)))

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem localAddress_injective
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    Function.Injective (localAddress vE cE iE jE v c valid i₀ j₀) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      have hval : a.val = b.val := congrArg Prod.snd (Sum.inl.inj h')
      exact congrArg Sum.inl (Subtype.ext hval)
    | inr b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      cases h'
  | inr a =>
    cases b with
    | inl b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      cases h'
    | inr b =>
      have h' := (globalEncoding vE cE iE jE).code.injective h
      have hext := congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj h'))
      exact congrArg Sum.inr (Subtype.ext (extendRestricted_injective valid hext))

def conditionedOccurrence
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    Equation (Fin (globalEncoding vE cE iE jE).size) :=
  mapEquation (localAddress vE cE iE jE v c valid i₀ j₀)
    (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedOccurrence_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (bits : Fin (globalEncoding vE cE iE jE).size → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ) bits =
      !(foldedAnswer i₀ (fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))) f ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) g ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) (thirdQuery π f g μ)) := by
  rw [conditionedOccurrence, satisfied_mapEquation]
  let tableA : HalfCube i₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))
  let tableB : HalfCube j₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code
      (.inr (.inl (c, extendRestricted valid h.val))))
  have hbits : bits ∘ localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment tableA tableB := by
    funext a
    cases a <;> rfl
  rw [hbits]
  exact FoldedEquation.conditionedEquation_satisfied valid π i₀ j₀ tableA tableB f g μ

end LocalEquations

/-- A terminating first-valid search on the explicitly ordered ambient list. -/
def findValid {J : Type} (valid : J → Bool) : List J → Option {j : J // valid j = true}
  | [] => none
  | j :: rest => if h : valid j = true then some ⟨j, h⟩ else findValid valid rest

theorem findValid_none_iff {J : Type} (valid : J → Bool) (xs : List J) :
    findValid valid xs = none ↔ ∀ j ∈ xs, valid j = false := by
  induction xs with
  | nil => simp [findValid]
  | cons j xs ih =>
    by_cases hj : valid j = true
    · simp [findValid, hj]
    · simp [findValid, hj, ih]

def firstValid {J : Type} (e : Encoding J) (valid : J → Bool) :
    Option {j : J // valid j = true} := findValid valid e.enumerate

theorem firstValid_none_iff {J : Type} (e : Encoding J) (valid : J → Bool) :
    firstValid e valid = none ↔ ∀ j, valid j = false := by
  rw [firstValid, findValid_none_iff]
  exact ⟨fun h j => h j (e.mem_enumerate j), fun h j _ => h j⟩

/-- Mapping the ordered enumeration preserves all sampled occurrences. -/
def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]

private theorem countP_cast_eq_sum_inline_SourceOccurrences {α : Type} (xs : List α) (p : α → Bool) :
    (xs.countP p : ℝ) = (xs.map (fun x => if p x then (1 : ℝ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih, add_comm]

theorem countP_enumerate {Tape : Type} [Fintype Tape]
    (tape : Encoding Tape) (p : Tape → Bool) :
    (tape.enumerate.countP p : ℝ) = ∑ x, if p x then (1 : ℝ) else 0 := by
  rw [countP_cast_eq_sum_inline_SourceOccurrences]
  simp only [Encoding.enumerate, List.map_ofFn, List.sum_ofFn]
  exact Fintype.sum_equiv tape.code.symm _ _ (fun _ => rfl)

/-- Exact satisfaction fraction of the actual ordered equation list equals
the uniform random-tape expectation, even when equations or addresses repeat. -/
theorem occurrenceList_acceptance {Tape Name : Type} [Fintype Tape]
    (tape : Encoding Tape) (emit : Tape → Equation Name) (bits : Name → Bool) :
    ((occurrenceList tape emit).countP (fun e => satisfied e bits) : ℝ) /
        (occurrenceList tape emit).length =
      𝔼 x, if satisfied (emit x) bits then (1 : ℝ) else 0 := by
  rw [occurrenceList_length, Fintype.expect_eq_sum_div_card, tape.card_eq_size]
  congr 1
  simpa only [occurrenceList, List.countP_map, Function.comp_def] using
    countP_enumerate tape (fun x => satisfied (emit x) bits)

open SourceContexts
open MaxCutGames.Reduction.FiniteNoise

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

/-- Independent actual half-tables extend to the explicit padded key space.
Only the canonically selected right anchor is read at each clause context. -/
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

/-- The private query law depends only on the two visible contexts.
In particular, the hidden sampled slots are not inputs to `pi`. -/
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

/-- The entire finite random-tape population, including repeated visible
contexts and all equation multiplicities, in a fixed explicit order. -/
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

/-- A satisfiable totalization for the empty input formula, without changing
or diluting the occurrence list of a nonempty formula. -/
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
    MaxCutGames.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩

theorem emptyFormulaEquation_satisfied (F : Target.Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) :
    satisfied (emptyFormulaEquation F u) bits = !(bits (dummyIndex F u)) := by
  cases h : bits (dummyIndex F u) <;> simp [emptyFormulaEquation, satisfied, h]

end MaxCutGames.Foundations.Hastad.SourceOccurrences

section

namespace MaxCutGames.Foundations.Hastad.SourceOccurrences.Encoding

variable {α β γ : Type}

theorem prod_decode_pair (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size) :
    (a.prod b).code.symm (finProdFinEquiv (i, j)) =
      (a.code.symm i, b.code.symm j) := by
  change (a.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1,
    b.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem prod_decode_mk (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size)
    (h : i.val * b.size + j.val < a.size * b.size) :
    (a.prod b).code.symm ⟨i.val * b.size + j.val, h⟩ =
      (a.code.symm i, b.code.symm j) := by
  have he : (⟨i.val * b.size + j.val, h⟩ : Fin (a.size * b.size)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  change (a.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).1,
    b.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).2) = _
  rw [he]
  exact prod_decode_pair a b i j

/-- Increasing product rank enumerates the first factor outside and the
second factor inside, including when either factor is empty. -/
theorem enumerate_prod (a : Encoding α) (b : Encoding β) :
    (a.prod b).enumerate =
      a.enumerate.flatMap (fun x => b.enumerate.map (fun y => (x, y))) := by
  change List.ofFn (fun q : Fin (a.size * b.size) =>
    (a.code.symm (finProdFinEquiv.symm q).1,
     b.code.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [enumerate, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact prod_decode_mk a b i j _

theorem map_enumerate_prod (a : Encoding α) (b : Encoding β) (emit : α × β → γ) :
    (a.prod b).enumerate.map emit =
      a.enumerate.flatMap (fun x => b.enumerate.map (fun y => emit (x, y))) := by
  rw [enumerate_prod]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

end MaxCutGames.Foundations.Hastad.SourceOccurrences.Encoding

namespace MaxCutGames.Foundations.Hastad.SourceEnumeration

open Target SourceContexts SourceOccurrences

/-- The exact tape order is left query, noise assignment, right query. -/
theorem testTapeEncoding_enumerate (u D : ℕ) :
    (testTapeEncoding u D).enumerate =
      ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
        ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
          ((jEncoding u).function Encoding.bool).enumerate.map (fun g => (f, z, g)))) := by
  simp only [testTapeEncoding, Encoding.enumerate_prod, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem sourceIndexEncoding_enumerate (F : Formula) (u D : ℕ) :
    (sourceIndexEncoding F u D).enumerate =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => ((c, s), (f, z, g))))))) := by
  simp only [sourceIndexEncoding, Encoding.enumerate_prod, testTapeEncoding_enumerate,
    List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

theorem sourceIndexEncoding_map {α : Type} (F : Formula) (u D : ℕ)
    (emit : SourceIndex F u D → α) :
    (sourceIndexEncoding F u D).enumerate.map emit =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => emit ((c, s), (f, z, g))))))) := by
  rw [sourceIndexEncoding_enumerate]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- The concrete equation list is exactly a nest of finite emitting loops. -/
theorem rawSourceList_eq_nestedLoops (F : Formula) (u D : ℕ) :
    rawSourceList F u D =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => contextEquation F u D c (sampledVariables F c s) (f, z, g)))))) := by
  exact sourceIndexEncoding_map F u D (sourceEquation F u D)

theorem sourceList_eq_nestedLoops (F : Formula) (u D : ℕ) (hne : F.clauses ≠ []) :
    sourceList F u D =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => contextEquation F u D c (sampledVariables F c s) (f, z, g)))))) := by
  rw [sourceList_nonempty F u D hne]
  exact rawSourceList_eq_nestedLoops F u D

/-- An output-word encoder can be concatenated directly in the same order.
This is an algebraic serialization identity, not a machine realization. -/
theorem rawSourceList_flatMap {α : Type} (F : Formula) (u D : ℕ)
    (emit : MaxCutGames.Reduction.CloneGap.Equation (Fin (nBits F u)) → List α) :
    (rawSourceList F u D).flatMap emit =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.flatMap
                (fun g => emit (contextEquation F u D c (sampledVariables F c s) (f, z, g))))))) := by
  rw [rawSourceList_eq_nestedLoops]
  simp only [List.flatMap_assoc, List.flatMap_map]

end MaxCutGames.Foundations.Hastad.SourceEnumeration

end

namespace MaxCutGames.Foundations.Hastad.SourceAddressArithmetic

open scoped BigOperators
open Target SourceContexts SourceOccurrences

theorem variable_rank (F : Formula) (u : ℕ) (v : VariableContext F u) :
    ((variableEncoding F u).code v).val =
      ∑ t : Fin u, (v t).val * F.«variables» ^ t.val := rfl

theorem clause_rank (F : Formula) (u : ℕ) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val =
      ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val := rfl

theorem left_address (F : Formula) (u : ℕ) (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ((variableEncoding F u).code v).val := rfl

theorem right_address (F : Formula) (u : ℕ) (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.«variables» ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val) := rfl

theorem dummy_address (F : Formula) (u : ℕ) :
    (dummyIndex F u).val =
      F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u) := by
  change F.«variables» ^ u * 2 ^ (2 ^ u) +
    (F.clauses.length ^ u * 2 ^ (8 ^ u) + 0) = _
  omega

theorem left_address_radix (F : Formula) (u : ℕ)
    (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ∑ t : Fin u, (v t).val * F.«variables» ^ t.val := by
  rw [left_address, variable_rank]

theorem right_address_radix (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.«variables» ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val) := by
  rw [right_address, clause_rank]

theorem nBits_eq_dummy_succ (F : Formula) (u : ℕ) :
    nBits F u = (dummyIndex F u).val + 1 := by
  rw [dummy_address, nBits_eq]
  omega

end MaxCutGames.Foundations.Hastad.SourceAddressArithmetic

namespace MaxCutGames.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

/-- All local control data have sizes determined solely by the repetition
parameter. Global variable and clause indices are absent. -/
structure Signature (u : ℕ) where
  signs : Position u → Bool
  sameName : NameProfile u
  selected : SlotContext u
  deriving DecidableEq

def signatureEquiv (u : ℕ) :
    Signature u ≃ (Position u → Bool) × NameProfile u × SlotContext u where
  toFun σ := (σ.signs, σ.sameName, σ.selected)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv σ := by cases σ; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

instance signatureFintype (u : ℕ) : Fintype (Signature u) :=
  Fintype.ofEquiv ((Position u → Bool) × NameProfile u × SlotContext u)
    (signatureEquiv u).symm

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

/-- A finite control alphabet bound, not a claim about evaluation time. -/
theorem card_signature (u : ℕ) :
    Fintype.card (Signature u) =
      2 ^ (3 * u) * ((2 ^ (3 * u)) ^ (3 * u) * 3 ^ u) := by
  rw [Fintype.card_congr (signatureEquiv u)]
  simp [NameProfile, Nat.mul_comm]

def positiveAt {n : ℕ} (clause : Clause n) : Slot → Bool
  | .first => clause[0].positive
  | .second => clause[1].positive
  | .third => clause[2].positive

def occurrenceName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (p : Position u) : Fin F.«variables» :=
  nameAt (clauseAt F (c p.1)) p.2

/-- The equality matrix can be supplied by a separate field-comparison
procedure after an explicit reindexing of the `3*u` positions. -/
def contextNameProfile (F : Formula) {u : ℕ} (c : ClauseContext F u) : NameProfile u :=
  fun p q => decide (occurrenceName F c p = occurrenceName F c q)

def ofContext (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (selected : SlotContext u) : Signature u where
  signs p := positiveAt (clauseAt F (c p.1)) p.2
  sameName := contextNameProfile F c
  selected := selected

@[simp] theorem ofContext_signs (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p : Position u) :
    (ofContext F c s).signs p = positiveAt (clauseAt F (c p.1)) p.2 := rfl

@[simp] theorem ofContext_sameName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p q : Position u) :
    (ofContext F c s).sameName p q =
      decide (occurrenceName F c p = occurrenceName F c q) := rfl

@[simp] theorem ofContext_selected (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : (ofContext F c s).selected = s := rfl

/-- Local clause truth is computed from signs and the three answer bits. -/
def signatureSatisfies {u : ℕ} (σ : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (σ.signs (t, .first)) (j t).first ||
    literalValue (σ.signs (t, .second)) (j t).second) ||
    literalValue (σ.signs (t, .third)) (j t).third

def signatureValid {u : ℕ} (σ : Signature u) (j : J u) : Bool :=
  decide ((∀ t, signatureSatisfies σ j t = true) ∧
    ∀ t t' s s', σ.sameName (t, s) (t', s') = true →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem signatureSatisfies_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u) (t : Fin u) :
    signatureSatisfies (ofContext F c s) j t =
      localSatisfies (clauseAt F (c t)) (j t) := rfl

/-- Exact equality with the actual contextual validity predicate, for every
answer tuple, including repeated «variables» within or across clauses. -/
theorem signature_validJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureValid (ofContext F c s) j = validJ F c j := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hs := of_decide_eq_true h
    apply (validJ_eq_true_iff F c j).mpr
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).symm.trans (hs.1 t)
    · intro t t' a a' hname
      apply hs.2 t t' a a'
      exact decide_eq_true hname
  · intro h
    have hs := (validJ_eq_true_iff F c j).mp h
    apply decide_eq_true
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).trans (hs.1 t)
    · intro t t' a a' heq
      exact hs.2 t t' a a' (of_decide_eq_true heq)

/-- The first slot matching the visible selected name, computed using only
the equality matrix. The selected slot guarantees visible support. -/
def signatureCanonicalSlot {u : ℕ} (σ : Signature u) (t : Fin u) : Slot :=
  if σ.sameName (t, .first) (t, σ.selected t) then .first
  else if σ.sameName (t, .second) (t, σ.selected t) then .second else .third

def signatureProjection {u : ℕ} (σ : Signature u) (j : J u) : I u :=
  fun t => answerAt (j t) (signatureCanonicalSlot σ t)

theorem signatureCanonicalSlot_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (t : Fin u) :
    signatureCanonicalSlot (ofContext F c s) t =
      canonicalSlot (clauseAt F (c t)) (sampledVariables F c s t) := by
  by_cases hfirst : nameAt (clauseAt F (c t)) .first =
      nameAt (clauseAt F (c t)) (s t)
  · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
      occurrenceName, sampledVariables, hfirst]
  · by_cases hsecond : nameAt (clauseAt F (c t)) .second =
        nameAt (clauseAt F (c t)) (s t)
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]

/-- The actual canonical projection factors through the finite signature on
every label, without a validity hypothesis. -/
theorem signature_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureProjection (ofContext F c s) j = pi F c (sampledVariables F c s) j := by
  funext t
  simp only [signatureProjection, signatureCanonicalSlot_ofContext, pi]

/-- On valid labels, canonical projection also agrees with the actual
selected occurrence answers. -/
theorem signature_projection_selected (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u)
    (hj : signatureValid (ofContext F c s) j = true) :
    signatureProjection (ofContext F c s) j = fun t => answerAt (j t) (s t) := by
  rw [signature_pi]
  have hv : validJ F c j = true := by simpa only [signature_validJ] using hj
  funext t
  exact (sampled_eq_pi F c (sampledVariables F c s) j hv t (s t) rfl).symm

/-- The same finite signature gives the same validity decision even across
formulas having different global index types. -/
theorem validJ_eq_of_signature_eq (F G : Formula) {u : ℕ}
    (c : ClauseContext F u) (d : ClauseContext G u) (s s' : SlotContext u)
    (h : ofContext F c s = ofContext G d s') (j : J u) :
    validJ F c j = validJ G d j := by
  rw [← signature_validJ F c s, h, signature_validJ]

theorem pi_eq_of_signature_eq (F G : Formula) {u : ℕ}
    (c : ClauseContext F u) (d : ClauseContext G u) (s s' : SlotContext u)
    (h : ofContext F c s = ofContext G d s') (j : J u) :
    pi F c (sampledVariables F c s) j = pi G d (sampledVariables G d s') j := by
  rw [← signature_pi F c s, h, signature_pi]

end MaxCutGames.Foundations.Hastad.SourceLocalSignature

end OAI
