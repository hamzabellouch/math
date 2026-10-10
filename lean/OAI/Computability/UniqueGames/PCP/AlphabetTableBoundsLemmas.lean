import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.PCP.AlphabetGraphLemmas
import OAI.Computability.UniqueGames.PCP.NameCompaction
import OAI.Computability.UniqueGames.PCP.Table

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

/-- The actual table output obeys the real gap bound, with no rational
approximation and with empty input dart sets allowed. -/
theorem gap_transfer_real (hq : 0 < q) (input : GenericGraphTables.Table q)
    (eps : ℝ) (eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      eps * (input.darts : ℝ) ≤
        ((GenericGraphTables.semantics input).rejectionCount labeling : ℝ))
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    (eps / 12288) * ((Table.build input).darts : ℝ) ≤
      ((GraphTables.semantics (Table.build input)).rejectionCount labeling : ℝ) := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraphBounds.gap_transfer_real
    (GenericGraphTables.semantics input) eps eps_nonnegative
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

/-- Exact output vertex count; this arithmetic identity also permits `q = 0`. -/
theorem build_vertices (input : GenericGraphTables.Table q) :
    (Table.build input).vertices = input.vertices * 2 ^ q +
      input.darts * AlphabetGraphBounds.vertexFactor q := by
  rw [Table.build_vertices]
  simp only [Enumeration.vertexCount, Enumeration.eventCount, Enumeration.addressCount,
    Enumeration.localCount, Enumeration.tapeCount, Enumeration.pairTapeCount,
    Enumeration.fiveTapeCount, AlphabetGraphBounds.vertexFactor,
    AlphabetGraphBounds.localEventFactor]
  ring

/-- Exact output dart count, including orientation and query multiplicity. -/
theorem build_darts (input : GenericGraphTables.Table q) :
    (Table.build input).darts = input.darts * AlphabetGraphBounds.dartFactor q := by
  rw [Table.build_darts]
  simp only [Enumeration.dartCount, Enumeration.eventCount, Enumeration.localCount,
    Enumeration.tapeCount, Enumeration.pairTapeCount, Enumeration.fiveTapeCount,
    AlphabetGraphBounds.dartFactor, AlphabetGraphBounds.localEventFactor]
  ring

theorem build_total (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts =
      input.vertices * 2 ^ q + input.darts *
        (AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q) := by
  rw [build_vertices, build_darts]
  ring

/-- A fixed alphabet gives one linear bound on the actual output table size. -/
theorem build_total_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) := by
  rw [build_total]
  have hv : 2 ^ q ≤ AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    omega
  have he : AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q ≤
      AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ input.vertices * AlphabetGraphBounds.sizeFactor q +
        input.darts * AlphabetGraphBounds.sizeFactor q :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

theorem build_vertices_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) :=
  (Nat.le_add_right _ _).trans (build_total_le input)

theorem build_darts_le (input : GenericGraphTables.Table q) :
    (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) :=
  (Nat.le_add_left _ _).trans (build_total_le input)

theorem sizeFactor_positive : 0 < AlphabetGraphBounds.sizeFactor q :=
  AlphabetGraphBounds.sizeFactor_positive q

end UniqueGamesTheorem.Foundations.PCP.AlphabetTableBounds

end

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

abbrev Pattern (q : Nat) := Fin q → Bool

/-- The enumeration visits only the fixed-size truth table, never proof assignments. -/
def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

/-- Finite test data, with no soundness or complexity assumption. -/
structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.variables + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.variables) : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.variables (finProdFinEquiv (finProdFinEquiv (e, p), j))

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.variables + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.variables) :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.variables :=
  ⟨V.query e i, !(patternAt q p i)⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.variables → Bool :=
  fun v => B (oldIndex V v)

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

/-- A computable assignment extension: finite-sum splitting and quotient/remainder
decoding recover the event, pattern, and auxiliary-bit indices. -/
def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (v : Fin V.variables) :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem convert_nonempty {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (eventsPositive : 0 < V.events) : (convert V hq).clauses ≠ [] := by
  have p : 0 < (convert V hq).clauses.length := by
    rw [convert_clause_count]
    exact Nat.mul_pos eventsPositive (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega))
  intro empty
  simp only [empty, List.length_nil] at p
  omega

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

/-- The actual answer pattern forces a failed chain, even when queried names
repeat and regardless of the labels on all allocated auxiliary variables. -/
theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

theorem convert_gap {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (a b : Nat)
    (gap : ∀ A, a * V.events ≤ b * rejectedEventCount V A)
    (B : Fin (outputVariables V) → Bool) :
    a * (convert V hq).clauses.length ≤
      (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by
  have eventGap := gap (restrictAssignment V B)
  have countBound := Nat.mul_le_mul_left b (convert_count_bridge V hq B)
  rw [convert_clause_count]
  calc
    a * (V.events * (2 ^ q * (q - 2))) = (a * V.events) * (2 ^ q * (q - 2)) := by
      rw [Nat.mul_assoc]
    _ ≤ (b * NameCompaction.failedCount (convert V hq) B) * (2 ^ q * (q - 2)) :=
      Nat.mul_le_mul_right _ (eventGap.trans countBound)
    _ = (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by ac_rfl

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

def padLiteral {n : Nat} (l : Literal n) : Literal (n + 1) :=
  ⟨Fin.castAdd 1 l.variableIndex, l.positive⟩

def padClause {n : Nat} (clause : Clause n) : Clause (n + 1) :=
  #v[padLiteral clause[0], padLiteral clause[1], padLiteral clause[2]]

def padTautology (n : Nat) : Clause (n + 1) :=
  let v := Fin.natAdd n (0 : Fin 1)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def padInput (F : Formula) : Formula where
  «variables» := F.variables + 1
  clauses := F.clauses.map padClause ++ [padTautology F.variables]

theorem padClause_eval {n : Nat} (c : Clause n) (B : Fin (n + 1) → Bool) :
    (padClause c).eval B = c.eval (fun v => B (Fin.castAdd 1 v)) := rfl

theorem padTautology_satisfied (n : Nat) (B : Fin (n + 1) → Bool) :
    (padTautology n).eval B = true := by
  simp [padTautology, Clause.eval, Literal.eval]

theorem padInput_satisfiable_iff (F : Formula) : (padInput F).Satisfiable ↔ F.Satisfiable := by
  change (∃ B : Fin (F.variables + 1) → Bool,
    ∀ c ∈ F.clauses.map padClause ++ [padTautology F.variables], c.eval B = true) ↔ _
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨fun v => B (Fin.castAdd 1 v), fun c hc => ?_⟩
    have hmem : padClause c ∈ (padInput F).clauses := by
      apply List.mem_append.mpr
      exact Or.inl (List.mem_map.mpr ⟨c, hc, rfl⟩)
    exact (padClause_eval c B).symm.trans (hB _ hmem)
  · rintro ⟨A, hA⟩
    let B : Fin (F.variables + 1) → Bool := Fin.addCases A (fun _ => false)
    refine ⟨B, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with original | padding
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp original
      have h := hA d hd
      simpa only [padClause_eval, B, Fin.addCases_left] using h
    · have hc : c = padTautology F.variables := by simpa using padding
      subst c
      exact padTautology_satisfied F.variables B

@[simp] theorem padInput_clause_count (F : Formula) :
    (padInput F).clauses.length = F.clauses.length + 1 := by simp [padInput]

theorem padInput_nonempty (F : Formula) : (padInput F).clauses ≠ [] := by
  intro empty
  have size := padInput_clause_count F
  rw [empty, List.length_nil] at size
  omega

def prepareInput (F : Formula) : Formula := NameCompaction.compact (padInput F)

theorem prepareInput_satisfiable_iff (F : Formula) :
    (prepareInput F).Satisfiable ↔ F.Satisfiable :=
  (NameCompaction.compact_satisfiable_iff (padInput F)).trans (padInput_satisfiable_iff F)

theorem prepareInput_clause_count (F : Formula) :
    (prepareInput F).clauses.length = F.clauses.length + 1 := by
  simp only [prepareInput, NameCompaction.compact_clause_count, padInput_clause_count]

theorem prepareInput_nonempty (F : Formula) : (prepareInput F).clauses ≠ [] := by
  intro empty
  have h := prepareInput_clause_count F
  rw [empty, List.length_nil] at h
  omega

theorem prepareInput_variable_bound (F : Formula) :
    (prepareInput F).variables ≤ 3 * (F.clauses.length + 1) := by
  simpa only [prepareInput, padInput_clause_count] using NameCompaction.compact_active_bound (padInput F)

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
