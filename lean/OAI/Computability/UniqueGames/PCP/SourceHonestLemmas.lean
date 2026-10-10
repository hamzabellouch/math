import OAI.Computability.UniqueGames.Machines.MachineRadixStepLemmas
import OAI.Computability.UniqueGames.PCP.ClauseVerifierLemmas
import OAI.Computability.UniqueGames.PCP.FoldedEquationLemmas
import OAI.Computability.UniqueGames.PCP.HonestTestLemmas
import OAI.Computability.UniqueGames.PCP.SourceAddressArithmeticLemmas
import OAI.Computability.UniqueGames.PCP.SourceOccurrences

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHonest

open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise
open scoped BigOperators

/-- Padded query tables are evaluated at one coordinate per context. Left and
right tables have disjoint tags, and the unused dummy bit is fixed to false. -/
def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl (c, g)) => g (right c)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl (c, g))) = g (right c) := rfl

/-- Extending a conditioned half-table into padded ambient storage does not
change its honest bit. Only correctness on valid coordinates is required. -/
theorem taggedAssignment_right_restriction {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (valid : J → Bool)
    (honest : {j : J // valid j = true}) (hright : right c = honest.val)
    (extend : Cube {j : J // valid j = true} → Cube J)
    (hextend : ∀ (g : Cube {j : J // valid j = true})
      (j : {j : J // valid j = true}), extend g j.val = g j)
    (j₀ : {j : J // valid j = true}) (h : HalfCube j₀) :
    taggedAssignment left right (.inr (.inl (c, extend h.val))) = h.val honest := by
  change extend h.val (right c) = h.val honest
  rw [hright]
  exact hextend h.val honest

section Local

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- Each honest emitted equation fails exactly when its selected noise bit is
true. This is a pointwise statement, before averaging any random tape. -/
theorem conditioned_equation_honest_satisfied
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i)
    (f : Cube I) (g μ : Cube J) :
    satisfied (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)
        (FoldedEquation.storedAssignment (fun h => h.val i) (fun h => h.val j)) =
      !(μ j.val) := by
  rw [FoldedEquation.conditionedEquation_satisfied, foldedAnswer_dictator,
    conditionedFoldedAnswer_dictator, conditionedFoldedAnswer_dictator,
    dictator_test_parity π i j.val hπ]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- Local table equalities are enough to reuse the same assignment even when
different occurrences, contexts, or query positions name the same proof bit. -/
theorem mapped_conditioned_equation_honest_satisfied {Name : Type}
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i)
    (rename : FoldedEquation.Address i₀ j₀ → Name) (assignment : Name → Bool)
    (hleft : ∀ h, assignment (rename (.inl h)) = h.val i)
    (hright : ∀ h, assignment (rename (.inr h)) = h.val j)
    (f : Cube I) (g μ : Cube J) :
    satisfied (mapEquation rename
        (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)) assignment =
      !(μ j.val) := by
  have hlocal : assignment ∘ rename =
      FoldedEquation.storedAssignment (fun h => h.val i) (fun h => h.val j) := by
    funext a
    cases a with
    | inl h => exact hleft h
    | inr h => exact hright h
  rw [satisfied_mapEquation, hlocal]
  exact conditioned_equation_honest_satisfied valid π i₀ i j₀ j hπ f g μ

/-- The exact finite noise law gives honest acceptance for a conditioned right
table and an unconditioned left table, with arbitrary fixed folding bases. -/
theorem tapeAcceptance_conditioned_dictators {D : ℕ} (positive : 0 < D)
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i) :
    SourceTape.tapeAcceptance D π
      (foldedAnswer i₀ (fun h => h.val i))
      (conditionedFoldedAnswer valid j₀ (fun h => h.val j)) =
        1 - (D : ℝ)⁻¹ := by
  rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
  exact realizedTestAcceptance_folded_conditioned_dictators positive π i₀ i valid j₀ j hπ

end Local

section NumberedStorage

open SourceOccurrences

variable {V C I J : Type}

/-- Numbering the global proof and then restricting it to one local table
recovers exactly the local honest half-tables. -/
theorem numbered_assignment_restriction
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (i₀ : I) (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) :
    assignmentOfKey vE cE iE jE (taggedAssignment left right) ∘
      localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment (fun h => h.val (left v)) (fun h => h.val j) := by
  funext a
  cases a with
  | inl h =>
    simp only [Function.comp_apply, localAddress, assignmentOfKey_code,
      taggedAssignment_left, FoldedEquation.storedAssignment, Sum.elim_inl]
  | inr h =>
    simp only [Function.comp_apply, localAddress, assignmentOfKey_code,
      taggedAssignment_right, hright, extendRestricted_valid,
      FoldedEquation.storedAssignment, Sum.elim_inr]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The globally numbered honest proof satisfies each actual occurrence
precisely when the corresponding noise bit is false. -/
theorem conditionedOccurrence_honest_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) (hπ : π j.val = left v)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ)
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)) = !(μ j.val) := by
  rw [conditionedOccurrence, satisfied_mapEquation,
    numbered_assignment_restriction vE cE iE jE left right v c valid i₀ j₀ j hright]
  exact conditioned_equation_honest_satisfied valid π i₀ (left v) j₀ j hπ f g μ

/-- Exact normalized accepted count for the actual ordered random-tape list
at one incidence context. Equal equations remain separate occurrences. -/
theorem conditionedOccurrenceList_honest_acceptance {D : ℕ} (positive : 0 < D)
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) (hπ : π j.val = left v)
    (tape : Encoding (SourceTape.TestTape I J D)) :
    let equations := occurrenceList tape (fun t =>
      conditionedOccurrence vE cE iE jE v c valid π i₀ j₀
        t.1 t.2.2 (realizedNoise t.2.1))
    ((equations.countP (fun e => satisfied e
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)))) : ℝ) /
        equations.length = 1 - (D : ℝ)⁻¹ := by
  dsimp only
  rw [occurrenceList_acceptance]
  calc
    _ = SourceTape.tapeAcceptance D π (fun f => f (left v)) (fun g => g j.val) := by
      unfold SourceTape.tapeAcceptance
      apply Finset.expect_congr rfl
      intro t _
      rw [conditionedOccurrence_honest_satisfied vE cE iE jE left right v c
        valid π i₀ j₀ j hright hπ, dictator_test_parity π (left v) j.val hπ]
      cases realizedNoise t.2.1 j.val <;> rfl
    _ = _ := by
      rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
      exact realizedTestAcceptance_dictator positive π (left v) j.val hπ

end NumberedStorage

open SourceContexts
open SourceOccurrences

/-- A single assignment to the globally tagged padded tables. It is defined
from the input assignment alone, before any incidence or test is sampled. -/
def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

/-- The same global proof in the construction's explicit radix numbering. -/
def honestBits (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
    (jEncoding u) (honestGlobal F u assignment)

@[simp] theorem honestBits_code (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool)
    (key : GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :
    honestBits F u assignment ((proofEncoding F u).code key) =
      honestGlobal F u assignment key :=
  assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u)
    (iEncoding u) (jEncoding u) (honestGlobal F u assignment) key

@[simp] theorem honestBits_dummy (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) :
    honestBits F u assignment (dummyIndex F u) = false := by
  rw [dummyIndex, honestBits_code]
  rfl

/-- Satisfiability supplies one consistent valid right coordinate in every
clause tuple, including tuples with repeated clauses or variable names. -/
def honestValidJ (F : Target.Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    {j : J u // validJ F c j = true} :=
  ⟨honestJ F c assignment, honestJ_valid F c assignment hs⟩

theorem validJ_nonempty_of_satisfying (F : Target.Formula) {u : ℕ}
    (c : ClauseContext F u) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    Nonempty {j : J u // validJ F c j = true} :=
  ⟨honestValidJ F c assignment hs⟩

theorem leftResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) (v : VariableContext F u) :
    leftResponse F u (honestBits F u assignment) v =
      fun f => f (honestI F v assignment) := by
  funext f
  simp only [leftResponse, honestBits_code, honestGlobal, taggedAssignment,
    foldedAnswer_dictator]

theorem rightResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (c : ClauseContext F u) :
    rightResponse F u (honestBits F u assignment) c =
      fun g => g (honestJ F c assignment) := by
  funext g
  cases ha : rightAnchor F c with
  | none =>
    have hf := (rightAnchor_none_iff F c).mp ha (honestJ F c assignment)
    rw [honestJ_valid F c assignment hs] at hf
    cases hf
  | some j₀ =>
    simp only [rightResponse, ha, honestBits_code, honestGlobal, taggedAssignment]
    have ht : (fun h : HalfCube j₀ =>
        extendRestricted (validJ F c) h.val (honestJ F c assignment)) =
        fun h => h.val (honestValidJ F c assignment hs) := by
      funext h
      exact extendRestricted_valid (validJ F c) h.val (honestValidJ F c assignment hs)
    rw [ht]
    exact conditionedFoldedAnswer_dictator (validJ F c) j₀
      (honestValidJ F c assignment hs) g

/-- Actual sampled incidence contexts attain the same honest finite-noise
acceptance. Folding bases may be chosen independently of the assignment. -/
theorem context_tapeAcceptance {D : ℕ} (positive : 0 < D)
    (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) (s : SlotContext u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (i₀ : I u) (j₀ : {j : J u // validJ F c j = true}) :
    SourceTape.tapeAcceptance D (pi F c (sampledVariables F c s))
      (foldedAnswer i₀ (fun h => h.val (honestI F (sampledVariables F c s) assignment)))
      (conditionedFoldedAnswer (validJ F c) j₀
        (fun h => h.val (honestValidJ F c assignment hs))) =
      1 - (D : ℝ)⁻¹ := by
  exact tapeAcceptance_conditioned_dictators positive (validJ F c)
    (pi F c (sampledVariables F c s)) i₀ _ j₀ _
    (pi_honest_sampled F c s assignment)

/-- The emitted equation, under the one global honest assignment, reads the
noise coordinate corresponding to the honest tuple of clause answers. -/
theorem sourceEquation_honest_satisfied (F : Target.Formula) (u D : ℕ)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (p : SourceIndex F u D) :
    satisfied (sourceEquation F u D p) (honestBits F u assignment) =
      !(realizedNoise p.2.2.1 (honestJ F p.1.1 assignment)) := by
  simp only [sourceEquation, contextEquation_satisfied, leftResponse_honest,
    rightResponse_honest F u assignment hs]
  rw [dictator_test_parity _ _ _ (pi_honest_sampled F p.1.1 p.1.2 assignment)]

/-- Every actual occurrence is counted, even when its visible context,
equation, or one of its three addresses repeats. -/
theorem rawSourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((rawSourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (rawSourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  have hc : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let : Nonempty (Fin F.clauses.length) := ⟨⟨0, hc⟩⟩
  rw [rawSourceList_acceptance F u D hD]
  have heq (c : ClauseContext F u) (s : SlotContext u) :
      testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
        (leftResponse F u (honestBits F u assignment) (sampledVariables F c s))
        (rightResponse F u (honestBits F u assignment) c) = 1 - (D : ℝ)⁻¹ := by
    rw [leftResponse_honest, rightResponse_honest F u assignment hs]
    exact testAcceptance_dictator _ _ _ _ (pi_honest_sampled F c s assignment)
  simp_rw [heq]
  simp only [Fintype.expect_const]

theorem sourceList_honest_acceptance_nonempty (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  rw [sourceList_nonempty F u D hF]
  exact rawSourceList_honest_acceptance F u D hD hF assignment hs

theorem sourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℝ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length := by
  by_cases hF : F.clauses = []
  · rw [sourceList_empty F u D hF]
    simp only [List.countP_cons, List.countP_nil, emptyFormulaEquation_satisfied,
      honestBits_dummy, Bool.not_false, ↓reduceIte,
      Nat.zero_add, Nat.cast_one, List.length_cons, List.length_nil, div_one]
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg D))
  · exact (sourceList_honest_acceptance_nonempty F u D hD hF assignment hs).ge

/-- Rational acceptance form used by the finite reduction interface. -/
theorem sourceList_honest_acceptance_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℚ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance F u D hD assignment hs

theorem sourceList_honest_acceptance_nonempty_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length = 1 - (D : ℚ)⁻¹ := by
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance_nonempty F u D hD hF assignment hs

end UniqueGamesTheorem.Foundations.Hastad.SourceHonest

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise

abbrev LocalKey (u : ℕ) := Cube (I u) ⊕ (Cube (J u) ⊕ Unit)
abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let position := (Encoding.fin u).prod slotEncoding
  let fields := (position.function Encoding.bool).prod
    ((position.function (position.function Encoding.bool)).prod (slotContextEncoding u))
  ⟨fields.size, (signatureEquiv u).trans fields.code⟩

def signatureList (u : ℕ) : List (Signature u) := (signatureEncoding u).enumerate

theorem mem_signatureList (u : ℕ) (σ : Signature u) : σ ∈ signatureList u :=
  (signatureEncoding u).mem_enumerate σ

theorem signatureList_nodup (u : ℕ) : (signatureList u).Nodup :=
  (signatureEncoding u).nodup_enumerate

theorem signatureList_length (u : ℕ) :
    (signatureList u).length = (signatureEncoding u).size :=
  (signatureEncoding u).length_enumerate

def localInputEncoding (u D : ℕ) : Encoding (LocalInput u D) :=
  (signatureEncoding u).prod (testTapeEncoding u D)

def localInputs (u D : ℕ) : List (LocalInput u D) := (localInputEncoding u D).enumerate

theorem mem_localInputs (u D : ℕ) (p : LocalInput u D) : p ∈ localInputs u D :=
  (localInputEncoding u D).mem_enumerate p

theorem localInputs_nodup (u D : ℕ) : (localInputs u D).Nodup :=
  (localInputEncoding u D).nodup_enumerate

theorem localInputs_length (u D : ℕ) :
    (localInputs u D).length = (localInputEncoding u D).size :=
  (localInputEncoding u D).length_enumerate

def localKeyEncoding (u : ℕ) : Encoding (LocalKey u) :=
  ((iEncoding u).function Encoding.bool).sum
    (((jEncoding u).function Encoding.bool).sum Encoding.unit)

def emptyLocalAddress (u : ℕ) : EmptyContext.Address (leftAnchor u) → LocalKey u
  | .inl f => .inl f.val
  | .inr _ => .inr (.inr ())

def foldedLocalAddress (u : ℕ) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    FoldedEquation.Address (leftAnchor u) j₀ → LocalKey u
  | .inl f => .inl f.val
  | .inr g => .inr (.inl (extendRestricted valid g.val))

/-- One local descriptor, reusing the existing folded and empty-context
equations. The first-valid search is over the fixed explicit answer encoding. -/
def equationFor (u D : ℕ) (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  match firstValid (jEncoding u) valid with
  | none => mapEquation (emptyLocalAddress u) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => mapEquation (foldedLocalAddress u valid j₀)
      (FoldedEquation.conditionedEquation valid π (leftAnchor u) j₀
        t.1 t.2.2 (realizedNoise t.2.1))

def equation (u D : ℕ) (σ : Signature u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  equationFor u D (signatureValid σ) (signatureProjection σ) t

def emit (u D : ℕ) (p : LocalInput u D) : Equation (LocalKey u) :=
  equation u D p.1 p.2

def addressMap (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) : LocalKey u → Fin (nBits F u)
  | .inl f => (proofEncoding F u).code (.inl (v, f))
  | .inr (.inl g) => (proofEncoding F u).code (.inr (.inl (c, g)))
  | .inr (.inr _) => dummyIndex F u

theorem mapEquation_comp {A B C : Type} (g : B → C) (f : A → B) (e : Equation A) :
    mapEquation g (mapEquation f e) = mapEquation (g ∘ f) e := rfl

theorem addressMap_emptyLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) :
    addressMap F u c v ∘ emptyLocalAddress u = emptyAddress F u v := by
  funext a
  cases a <;> rfl

theorem addressMap_foldedLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    addressMap F u c v ∘ foldedLocalAddress u valid j₀ =
      localAddress (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)
        v c valid (leftAnchor u) j₀ := by
  funext a
  cases a <;> rfl

/-- A generic factorization first aligns the validity function itself, so no
unproved transport of dependent anchor subtypes is needed. -/
theorem contextEquation_eq_map_equationFor (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c v t =
      mapEquation (addressMap F u c v) (equationFor u D (validJ F c) (pi F c v) t) := by
  unfold contextEquation equationFor rightAnchor
  cases h : firstValid (jEncoding u) (validJ F c) with
  | none =>
    rw [mapEquation_comp, addressMap_emptyLocalAddress]
  | some j₀ =>
    rw [mapEquation_comp, addressMap_foldedLocalAddress]
    rfl

theorem contextEquation_eq_map (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c (sampledVariables F c s) t =
      mapEquation (addressMap F u c (sampledVariables F c s))
        (equation u D (ofContext F c s) t) := by
  have hv : signatureValid (ofContext F c s) = validJ F c :=
    funext (signature_validJ F c s)
  have hp : signatureProjection (ofContext F c s) = pi F c (sampledVariables F c s) :=
    funext (signature_pi F c s)
  rw [equation, hv, hp]
  exact contextEquation_eq_map_equationFor F u D c (sampledVariables F c s) t

theorem sourceEquation_eq_map_emit (F : Formula) (u D : ℕ)
    (p : SourceIndex F u D) :
    sourceEquation F u D p =
      mapEquation (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (emit u D (ofContext F p.1.1 p.1.2, p.2)) :=
  contextEquation_eq_map F u D p.1.1 p.1.2 p.2

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open UniqueGamesTheorem.Reduction.CloneGap

abbrev Descriptor := Fin 3 × ℕ

def descriptor (u : ℕ) : LocalKey u → Descriptor
  | .inl f => (0, (((iEncoding u).function Encoding.bool).code f).val)
  | .inr (.inl g) => (1, (((jEncoding u).function Encoding.bool).code g).val)
  | .inr (.inr _) => (2, 0)

/-- Registers zero and one start the selected left and right query blocks;
register two is the single dummy address. -/
def baseValue (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) : ℕ :=
  if side = 0 then 2 ^ (2 ^ u) * ((variableEncoding F u).code v).val
  else if side = 1 then F.variables ^ u * 2 ^ (2 ^ u) +
    2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val
  else F.variables ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u)

def realize (base : Fin 3 → ℕ) (d : Descriptor) : ℕ := d.2 + base d.1

def words (base : Fin 3 → ℕ) (e : Equation Descriptor) : List ℕ :=
  [realize base e.first, realize base e.second, realize base e.third,
    if e.rhs then 1 else 0]

theorem realize_descriptor (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (key : LocalKey u) :
    realize (baseValue F u c v) (descriptor u key) = (addressMap F u c v key).val := by
  cases key with
  | inl f =>
      simpa [realize, descriptor, baseValue, addressMap] using
        (left_address F u v f).symm
  | inr key =>
      cases key with
      | inl g =>
          simp [realize, descriptor, baseValue, addressMap, right_address]
          omega
      | inr _dummy =>
          simp only [realize, descriptor, baseValue, show (2 : Fin 3) ≠ 0 by decide,
            show (2 : Fin 3) ≠ 1 by decide, ite_false, Nat.zero_add, addressMap,
            dummy_address]

theorem descriptor_offset_bound (u : ℕ) (key : LocalKey u) :
    (descriptor u key).2 < 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1 := by
  cases key with
  | inl f =>
      have h := (((iEncoding u).function Encoding.bool).code f).isLt
      change _ < 2 ^ (2 ^ u) at h
      change (((iEncoding u).function Encoding.bool).code f).val < _
      calc
        _ < (2 ^ (2 ^ u) : ℕ) := h
        _ ≤ 2 ^ (2 ^ u) + 2 ^ (8 ^ u) := Nat.le_add_right _ _
        _ ≤ _ := Nat.le_add_right _ _
  | inr key =>
      cases key with
      | inl g =>
          have h := (((jEncoding u).function Encoding.bool).code g).isLt
          change _ < 2 ^ (8 ^ u) at h
          change (((jEncoding u).function Encoding.bool).code g).val < _
          calc
            _ < (2 ^ (8 ^ u) : ℕ) := h
            _ ≤ 2 ^ (2 ^ u) + 2 ^ (8 ^ u) := Nat.le_add_left _ _
            _ ≤ _ := Nat.le_add_right _ _
      | inr _dummy => simp [descriptor]

theorem sourceEquation_numeric (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    mapEquation Fin.val (sourceEquation F u D p) =
      mapEquation (realize (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2)))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit, mapEquation_comp, mapEquation_comp]
  congr 1
  funext key
  exact (realize_descriptor F u p.1.1 (sampledVariables F p.1.1 p.1.2) key).symm

theorem sourceEquation_words (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [UniqueGamesTheorem.Reduction.SourceEncoding.equationWords, words, mapEquation]
  rw [realize_descriptor, realize_descriptor, realize_descriptor]
  rfl

theorem baseValue_lt (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) :
    baseValue F u c v side < nBits F u := by
  have hside : side = 0 ∨ side = 1 ∨ side = 2 := by omega
  rcases hside with rfl | rfl | rfl
  · have h := (addressMap F u c v (.inl (fun _ => false))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 0 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inl (fun _ => false)))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 1 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inr ()))).isLt
    rw [← realize_descriptor] at h
    simpa only [realize, descriptor, Nat.zero_add] using h

theorem equation_emit_steps_le (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (e : Equation Descriptor) :
    2 * (baseValue F u c v e.first.1 + baseValue F u c v e.second.1 +
      baseValue F u c v e.third.1) + 16 ≤ 6 * nBits F u + 16 := by
  have h₁ := (baseValue_lt F u c v e.first.1).le
  have h₂ := (baseValue_lt F u c v e.second.1).le
  have h₃ := (baseValue_lt F u c v e.third.1).le
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open UniqueGamesTheorem.Reduction.MachineSubstitution

inductive Label
  | seed
  | horner (label : MachineHorner.Label 2)
  | clear
  deriving DecidableEq, Fintype

abbrev Layout := MachineHorner.Layout 2

def digits (coefficient offset : Nat) (i : Nat) : Nat :=
  if i = 0 then coefficient else offset

theorem horner_value (coefficient rank offset : Nat) :
    MachineHorner.value rank (digits coefficient offset) 2 = coefficient * rank + offset := by
  simp [MachineHorner.value, digits, Nat.mul_comm]

def steps (coefficient rank offset : Nat) : Nat :=
  MachineHorner.steps rank (digits coefficient offset) 2 + coefficient + 2

def operandLength (rank offset : Nat) : Nat :=
  (encodeWord rank).length + (encodeWord offset).length

noncomputable def timePolynomial (coefficient : Nat) : Polynomial Nat :=
  (MachineHorner.timePolynomial 2).comp (Polynomial.X + Polynomial.C coefficient) +
    Polynomial.C (coefficient + 2)

theorem timePolynomial_eval (coefficient n : Nat) :
    (timePolynomial coefficient).eval n =
      (MachineHorner.timePolynomial 2).eval (n + coefficient) + coefficient + 2 := by
  simp [timePolynomial, Polynomial.eval_comp, Nat.add_assoc]

theorem steps_le_timePolynomial (coefficient rank offset : Nat) :
    steps coefficient rank offset ≤ (timePolynomial coefficient).eval (operandLength rank offset) := by
  have hr : rank ≤ operandLength rank offset + coefficient := by
    simp only [operandLength, encodeWord_length]
    omega
  have hd : ∀ i, i < 2 → digits coefficient offset i ≤ operandLength rank offset + coefficient := by
    intro i _
    simp only [digits, operandLength, encodeWord_length]
    split <;> omega
  have h := MachineHorner.steps_le_timePolynomial rank (digits coefficient offset) 2
    (operandLength rank offset + coefficient) hr hd
  rw [timePolynomial_eval]
  unfold steps
  omega

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .seed => pushWord (slots (.inr 0)) (encodeWord coefficient).reverse
      (.goto fun _ => labels (.horner .start))
  | .horner label => MachineHorner.statement slots (fun l => labels (.horner l))
      (some (labels .clear)) label
  | .clear => MachineHorner.drainLoop (slots (.inr 0)) (labels .clear) exit

def program (slots : Layout ↪ K) (coefficient : Nat) :
    Label → TM2.Stmt (fun _ : K => Bool) Label (MachineHorner.State σ) :=
  statement slots coefficient id none

def coefficientTapes (slots : Layout ↪ K) (base : K → List Bool) (coefficient : Nat) : K → List Bool :=
  Function.update base (slots (.inr 0)) (encodeWord coefficient)

/-- Exact affine execution, including coefficient initialization and cleanup. -/
theorem affineTrace (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps coefficient rank offset]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩ := by
  have hc (i : Fin 6) : slots (.inl i) ≠ slots (.inr 0) := slots.injective.ne (by simp)
  have hd : slots (.inr 1) ≠ slots (.inr 0) := slots.injective.ne (by decide)
  let seeded := coefficientTapes slots base coefficient
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (.horner .start)), ((ambient, ()), register), seeded⟩ := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      coefficientEmpty, List.append_nil, seeded, coefficientTapes]
  have hradix : seeded (slots (.inl 0)) = encodeWord rank := by
    simp [seeded, coefficientTapes, hc, rankWord]
  have hdigits : ∀ i : Fin 2, seeded (slots (.inr i)) = encodeWord (digits coefficient offset i.val) := by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp [seeded, coefficientTapes, digits]
    · simp [seeded, coefficientTapes, digits, hd, offsetWord]
  have hclean : MachineHorner.Clean slots seeded := {
    accA := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 1)] using clean.accA
    accB := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 2)] using clean.accB
    counter := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 4)] using clean.counter
    scratch := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 5)] using clean.scratch
  }
  have hhorner := MachineHorner.hornerTrace slots (fun l => labels (.horner l))
    (some (labels .clear)) p (fun l => atLabels (.horner l)) seeded rank
    (digits coefficient offset) hradix hdigits hclean ambient register
  rw [horner_value] at hhorner
  let after := MachineHorner.resultTapes slots seeded (coefficient * rank + offset)
  have hafter : after (slots (.inr 0)) = encodeWord coefficient := by
    simp [after, MachineHorner.resultTapes, Ne.symm (hc 3), seeded, coefficientTapes]
  have hstart : Function.update after (slots (.inr 0)) (encodeWord coefficient ++ []) = after := by
    rw [List.append_nil, ← hafter, Function.update_eq_self]
  have hfinish : Function.update after (slots (.inr 0)) [] =
      MachineHorner.resultTapes slots base (coefficient * rank + offset) := by
    funext k
    by_cases ho : k = slots (.inl 3)
    · subst k
      simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, hc 3]
    · by_cases hk : k = slots (.inr 0)
      · subst k
        simp [MachineHorner.resultTapes, Ne.symm (hc 3), coefficientEmpty]
      · simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, ho, hk]
  have hclear := MachineHorner.drainTrace (slots (.inr 0)) (labels .clear) exit p
    (atLabels .clear) after coefficient [] ambient none
  rw [hstart, hfinish] at hclear
  rw [show steps coefficient rank offset = (coefficient + 1) +
      (MachineHorner.steps rank (digits coefficient offset) 2 + 1) by unfold steps; omega,
    Function.iterate_add_apply, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[coefficient + 1]
    ((MachineComposition.advance (TM2.step p))^[MachineHorner.steps rank (digits coefficient offset) 2]
      ((MachineComposition.advance (TM2.step p))^[1]
        (some ⟨some (labels .seed), ((ambient, ()), register), base⟩))) = _
  rw [hseed, hhorner]
  exact hclear

def affineInTime (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      (steps coefficient rank offset) where
  steps := steps coefficient rank offset
  evals_in_steps := affineTrace slots coefficient labels exit p atLabels base rank offset
    rankWord offsetWord coefficientEmpty clean ambient register
  steps_le_m := Nat.le_refl _

def affineInPolynomialTime (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) where
  steps := steps coefficient rank offset
  evals_in_steps := affineTrace slots coefficient labels exit p atLabels base rank offset
    rankWord offsetWord coefficientEmpty clean ambient register
  steps_le_m := steps_le_timePolynomial coefficient rank offset

def programInTime (slots : Layout ↪ K) (coefficient : Nat) (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots coefficient))
      ⟨some .seed, ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) :=
  affineInPolynomialTime slots coefficient id none (program slots coefficient) (fun _ => rfl)
    base rank offset rankWord offsetWord coefficientEmpty clean ambient register

/-- Left query-block base from the preserved variable tuple rank and a zero offset field. -/
def leftBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (2 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((variableEncoding F u).code v).val))
    (zeroWord : base (slots (.inr 1)) = encodeWord 0)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 0)⟩)
      ((timePolynomial (2 ^ (2 ^ u))).eval (operandLength (((variableEncoding F u).code v).val) 0)) := by
  have h := affineInPolynomialTime slots (2 ^ (2 ^ u)) labels exit p atLabels base
    (((variableEncoding F u).code v).val) 0 rankWord zeroWord coefficientEmpty clean ambient register
  have hv : 2 ^ (2 ^ u) * (((variableEncoding F u).code v).val) + 0 = baseValue F u c v 0 := by
    simp [baseValue]
  simpa only [hv] using h

/-- Right query-block base using the globally retained left-block size. -/
def rightBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (8 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (leftBlockWord : base (slots (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.variables ^ u))
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 1)⟩)
      ((timePolynomial (2 ^ (8 ^ u))).eval
        (operandLength (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.variables ^ u))) := by
  have h := affineInPolynomialTime slots (2 ^ (8 ^ u)) labels exit p atLabels base
    (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.variables ^ u)
    rankWord leftBlockWord coefficientEmpty clean ambient register
  have hv : 2 ^ (8 ^ u) * (((clauseEncoding F u).code c).val) + 2 ^ (2 ^ u) * F.variables ^ u =
      baseValue F u c v 1 := by
    simp [baseValue, Nat.mul_comm, Nat.add_comm]
  simpa only [hv] using h

/-- The retained dummy register is among the unchanged external tapes. -/
theorem resultTapes_dummy (slots : Layout ↪ K) (base : K → List Bool) (value : Nat)
    (dummy : K) (distinct : dummy ≠ slots (.inl 3)) :
    MachineHorner.resultTapes slots base value dummy = base dummy :=
  MachineHorner.resultTapes_other slots base value dummy distinct

def machine (coefficient : Nat) : FinTM2 where
  K := Layout
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := MachineHorner.State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl Layout) coefficient

def machineInTime (coefficient rank offset : Nat) (base : Layout → List Bool)
    (rankWord : base (.inl 0) = encodeWord rank) (offsetWord : base (.inr 1) = encodeWord offset)
    (coefficientEmpty : base (.inr 0) = [])
    (clean : MachineHorner.Clean (Function.Embedding.refl _) base) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine coefficient).step
      ⟨some Label.seed, (((), ()), register), base⟩
      (some ⟨none, (((), ()), none),
        MachineHorner.resultTapes (Function.Embedding.refl _) base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) :=
  programInTime (Function.Embedding.refl _) coefficient base rank offset rankWord offsetWord
    coefficientEmpty clean () register

end UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

end OAI
