import Mathlib
import OAI.Computability.MaxCut.Games.TranslationTarget
import OAI.Computability.MaxCut.Games.Subdivision
import OAI.Computability.MaxCut.Machines.MachineBinaryFormula
import OAI.Computability.MaxCut.Machines.RuntimeSpace

namespace OAI

/-!
Soundness of the ordinary-binary parser and its concrete name-scanning machine.
Every successful parse consumes exactly a canonical encoding and leaves its
stated suffix. Thus malformed or noncanonical bitstrings cannot name an extra
formula. The finite scanner's final-digit test is proved equivalent to the
codec's arithmetic canonicality test.
-/

namespace MaxCutGames.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [BinaryNameMachine.frame, frame, ih]

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

/-- A payload has no redundant high zero precisely when its last digit is one,
with the empty payload representing zero. -/
theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

theorem parseFrame_sound (input digits rest : List Bool)
    (parsed : parseFrame input = some (digits, rest)) : input = frame digits ++ rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at parsed
  | singleton flag =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · simp [parseFrame] at parsed
  | cons_cons flag bit input ih _ =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · cases h : parseFrame input with
        | none => simp [parseFrame, h] at parsed
        | some pair =>
            rcases pair with ⟨ds, tail⟩
            have hs := ih ds tail h
            simp [parseFrame, h] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            simp [frame, hs]

theorem parseName_sound (input : List Bool) (name : Nat) (rest : List Bool)
    (parsed : parseName input = some (name, rest)) : input = nameBits name ++ rest := by
  cases h : parseFrame input with
  | none => simp [parseName, h] at parsed
  | some pair =>
      rcases pair with ⟨digits, tail⟩
      by_cases canonical : digits = (bitsValue digits).bits
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some] at parsed
        rw [ite_eq_left canonical] at parsed
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        have hs := parseFrame_sound input digits tail h
        exact hs.trans (congrArg (fun ds => frame ds ++ tail) canonical)
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some, ite_eq_right canonical] at parsed
        cases parsed

theorem parseLiteral_sound (input : List Bool) (literal : Literal) (rest : List Bool)
    (parsed : parseLiteral input = some (literal, rest)) :
    input = literalBits literal ++ rest := by
  cases input with
  | nil => simp [parseLiteral] at parsed
  | cons sign input =>
      cases h : parseName input with
      | none => simp [parseLiteral, h] at parsed
      | some pair =>
          rcases pair with ⟨name, tail⟩
          have hs := parseName_sound input name tail h
          simp [parseLiteral, h] at parsed
          rcases parsed with ⟨rfl, rfl⟩
          simp [literalBits, hs]

theorem parseClause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (parsed : parseClause input = some (clause, rest)) : input = clauseBits clause ++ rest := by
  cases ha : parseLiteral input with
  | none => simp [parseClause, ha] at parsed
  | some first =>
      rcases first with ⟨a, afterA⟩
      cases hb : parseLiteral afterA with
      | none => simp [parseClause, ha, hb] at parsed
      | some second =>
          rcases second with ⟨b, afterB⟩
          cases hc : parseLiteral afterB with
          | none => simp [parseClause, ha, hb, hc] at parsed
          | some third =>
              rcases third with ⟨c, afterC⟩
              have hA := parseLiteral_sound input a afterA ha
              have hB := parseLiteral_sound afterA b afterB hb
              have hC := parseLiteral_sound afterB c afterC hc
              have pairEq : (#v[a, b, c], afterC) = (clause, rest) := by
                apply Option.some.inj
                simpa only [parseClause, ha, hb, hc, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def] using parsed
              rcases Prod.mk.inj pairEq with ⟨rfl, rfl⟩
              simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem parseClauses_sound (fuel : Nat) (input : List Bool)
    (clauses : List Clause) (rest : List Bool)
    (parsed : parseClauses fuel input = some (clauses, rest)) :
    input = clausesBits clauses ++ rest := by
  induction fuel generalizing input clauses rest with
  | zero => simp [parseClauses] at parsed
  | succ fuel ih =>
      cases input with
      | nil => simp [parseClauses] at parsed
      | cons flag input =>
          cases flag
          · simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            rfl
          · cases hc : parseClause input with
            | none => simp [parseClauses, hc] at parsed
            | some first =>
                rcases first with ⟨clause, afterClause⟩
                cases hs : parseClauses fuel afterClause with
                | none => simp [parseClauses, hc, hs] at parsed
                | some remaining =>
                    rcases remaining with ⟨cs, tail⟩
                    have hC := parseClause_sound input clause afterClause hc
                    have hS := ih afterClause cs tail hs
                    simp [parseClauses, hc, hs] at parsed
                    rcases parsed with ⟨rfl, rfl⟩
                    simp [clausesBits, hC, hS, List.append_assoc]

theorem decodeFormula_sound (input : List Bool) (formula : Formula)
    (parsed : decodeFormula input = some formula) : input = formulaBits formula := by
  cases h : parseClauses (input.length + 1) input with
  | none => simp [decodeFormula, h] at parsed
  | some pair =>
      rcases pair with ⟨clauses, rest⟩
      by_cases empty : rest = []
      · subst rest
        simp [decodeFormula, h] at parsed
        subst formula
        simpa only [formulaBits, List.append_nil] using
          parseClauses_sound (input.length + 1) input clauses [] h
      · simp [decodeFormula, h, empty] at parsed

theorem decodeFormula_eq_some_iff (input : List Bool) (formula : Formula) :
    decodeFormula input = some formula ↔ input = formulaBits formula :=
  ⟨decodeFormula_sound input formula, fun h => h ▸ decodeFormula_encoded formula⟩

/-- Exact agreement of the finite-state name scanner with a canonical encoded
name, including the untouched suffix and the actual binary payload stack. -/
theorem scanSpec_nameBits (name : Nat) (suffix output : List Bool) :
    BinaryNameMachine.scanSpec (nameBits name ++ suffix) output none =
      ⟨true, suffix, name.bits.reverse ++ output⟩ := by
  unfold nameBits
  rw [← frame_eq, BinaryNameMachine.scanSpec_frame]
  have h := canonical_nat_bits name
  simpa only [BinaryNameMachine.canonical] using
    congrArg (fun accepted =>
      (⟨accepted, suffix, name.bits.reverse ++ output⟩ : BinaryNameMachine.Result)) h

end MaxCutGames.BinaryParsing

/-!
Occurrence-index renaming for the ordinary-binary input machine. Every name is
replaced by the position of its first occurrence in the complete literal-name
list. The output declares three «variables» per clause; some IDs can be unused.
This avoids constructing a duplicate-free dictionary while keeping all IDs
bounded by the literal occurrence count. Equality tests may compare the actual
canonical binary payloads, without converting a name to unary.

These are the correspondence facts for the scan/compare machine.
They do not by themselves assert that the renaming runs in polynomial time.
-/

namespace MaxCutGames.BinaryOccurrenceRename

open BinaryFormula MaxCutGames.Foundations

theorem literal_mem_names (F : Formula) (c : Clause) (hc : c ∈ F.clauses)
    (i : Fin 3) : (c)[i].name ∈ sourceNames F := by
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def nameIndex (F : Formula) (name : Nat) (mem : name ∈ sourceNames F) :
    Fin (sourceNames F).length :=
  ⟨(sourceNames F).idxOf name, List.idxOf_lt_length_of_mem mem⟩

def literal (F : Formula) (l : Literal) (mem : l.name ∈ sourceNames F) :
    Target.Literal (sourceNames F).length :=
  ⟨nameIndex F l.name mem, l.positive⟩

def clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Target.Clause (sourceNames F).length :=
  #v[literal F (c)[0] (literal_mem_names F c mem 0),
    literal F (c)[1] (literal_mem_names F c mem 1),
    literal F (c)[2] (literal_mem_names F c mem 2)]

def renamed (F : Formula) : Target.Formula where
  «variables» := (sourceNames F).length
  clauses := F.clauses.attach.map (fun c => clause F c.val c.property)

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (sourceNames F).length → Bool :=
  fun i => A (sourceNames F)[i.val]

def extendAssignment (F : Formula) (A : Fin (sourceNames F).length → Bool) : Nat → Bool :=
  fun name => if mem : name ∈ sourceNames F then A (nameIndex F name mem) else false

@[simp] theorem nameIndex_reads_name (F : Formula) (name : Nat)
    (mem : name ∈ sourceNames F) : (sourceNames F)[(nameIndex F name mem).val] = name :=
  List.getElem_idxOf _

@[simp] theorem clause_eval_restrict (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Nat → Bool) : (clause F c mem).eval (restrictAssignment F A) = c.eval A := by
  simp [clause, literal, Target.Clause.eval, Target.Literal.eval,
    BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, restrictAssignment]

@[simp] theorem clause_eval_extend (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Fin (sourceNames F).length → Bool) :
    (clause F c mem).eval A = c.eval (extendAssignment F A) := by
  have evalLiteral (l : Literal) (hl : l.name ∈ sourceNames F) :
      (literal F l hl).eval A = l.eval (extendAssignment F A) := by
    simp only [literal, Target.Literal.eval, BinaryFormula.Literal.eval,
      extendAssignment, dite_eq_left hl]
    rfl
  simp [clause, Target.Clause.eval, BinaryFormula.Clause.eval, evalLiteral]

@[simp] theorem renamed_clause_count (F : Formula) :
    (renamed F).clauses.length = F.clauses.length := by simp [renamed]

@[simp] theorem renamed_variable_count (F : Formula) :
    (renamed F).«variables» = 3 * F.clauses.length := by
  exact clauseNames_flat_length F.clauses

theorem renamed_satisfiable_iff (F : Formula) : (renamed F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨extendAssignment F A, ?_⟩
    intro c mem
    have hc : clause F c mem ∈ (renamed F).clauses :=
      List.mem_map.mpr ⟨⟨c, mem⟩, by simp, rfl⟩
    exact (clause_eval_extend F c mem A).symm.trans (hA _ hc)
  · rintro ⟨A, hA⟩
    refine ⟨restrictAssignment F A, ?_⟩
    intro c mem
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp mem
    exact (clause_eval_restrict F original.val original.property A).trans
      (hA original.val original.property)

theorem nat_bits_injective : Function.Injective Nat.bits := by
  intro a b same
  have decoded := congrArg BinaryEncoding.bitsValue same
  simpa only [BinaryEncoding.bitsValue_bits] using decoded

/-- The numerical first occurrence is exactly the index found by comparing
binary payload lists. This is the key search-machine correspondence. -/
theorem idxOf_binary_payloads (names : List Nat) (name : Nat) :
    (names.map Nat.bits).idxOf name.bits = names.idxOf name := by
  induction names with
  | nil => rfl
  | cons first names ih =>
      by_cases same : first = name
      · subst first
        simp
      · have different : first.bits ≠ name.bits := fun h => same (nat_bits_injective h)
        simp only [List.map_cons, List.idxOf_cons, beq_false_of_ne same,
          beq_false_of_ne different, ih]

/-- The fixed unary output codec has quadratic size in the literal count. -/
theorem renamed_encoding_bound (F : Formula) :
    (Complexity.formulaBits (renamed F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have h := Complexity.formulaBits_length_le (renamed F)
  simp only [renamed_clause_count, renamed_variable_count] at h
  nlinarith

theorem renamed_encoding_bound_bits (F : Formula) :
    (Complexity.formulaBits (renamed F)).length ≤
      9 * (BinaryEncoding.formulaBits F).length * (BinaryEncoding.formulaBits F).length +
      10 * (BinaryEncoding.formulaBits F).length + 2 := by
  have h := renamed_encoding_bound F
  have hm : F.clauses.length ≤ (BinaryEncoding.formulaBits F).length :=
    (BinaryEncoding.clauses_length_lt_bits F.clauses).le
  have hsq := Nat.mul_self_le_mul_self hm
  nlinarith

end MaxCutGames.BinaryOccurrenceRename

/-!
The ordinary binary 3SAT language includes exactly the successfully decoded
satisfiable formulas. A total semantic extension of occurrence-index renaming
maps malformed bitstrings to a fixed contradictory formula. Its runtime is a
separate machine-composition obligation; the size theorem below is only size.
-/

namespace MaxCutGames.BinaryLanguage

open MaxCutGames.Foundations

def rejectBinary : BinaryFormula.Formula where
  clauses := [#v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩],
    #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]

theorem rejectBinary_unsatisfiable : ¬rejectBinary.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied #v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩]
    (by simp [rejectBinary])
  have negative := satisfied #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]
    (by simp [rejectBinary])
  cases h : assignment 0 <;>
    simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at positive negative

def rejectFormula : Target.Formula := BinaryOccurrenceRename.renamed rejectBinary

theorem reject_unsatisfiable : ¬rejectFormula.Satisfiable := by
  simpa only [rejectFormula, BinaryOccurrenceRename.renamed_satisfiable_iff] using
    rejectBinary_unsatisfiable

def language (input : List Bool) : Prop :=
  ∃ formula, BinaryEncoding.decodeFormula input = some formula ∧ formula.Satisfiable

def totalParsed (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD rejectBinary

def totalRename (input : List Bool) : Target.Formula :=
  BinaryOccurrenceRename.renamed (totalParsed input)

theorem totalParsed_satisfiable_iff (input : List Bool) :
    (totalParsed input).Satisfiable ↔ language input := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none => simp [totalParsed, parsed, rejectBinary_unsatisfiable, language]
  | some formula => simp [totalParsed, parsed, language]

theorem totalRename_satisfiable_iff (input : List Bool) :
    (totalRename input).Satisfiable ↔ language input := by
  exact (BinaryOccurrenceRename.renamed_satisfiable_iff (totalParsed input)).trans
    (totalParsed_satisfiable_iff input)

theorem totalRename_encoded (formula : BinaryFormula.Formula) :
    totalRename (BinaryEncoding.formulaBits formula) = BinaryOccurrenceRename.renamed formula := by
  simp [totalRename, totalParsed]

theorem language_encoded (formula : BinaryFormula.Formula) :
    language (BinaryEncoding.formulaBits formula) ↔ formula.Satisfiable := by
  simp [language]

theorem reject_bits_length : (Complexity.formulaBits rejectFormula).length = 25 := by decide

theorem totalRename_output_length (input : List Bool) :
    (Complexity.formulaBits (totalRename input)).length ≤
      9 * input.length * input.length + 10 * input.length + 25 := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none =>
      have output : totalRename input = rejectFormula := by simp [totalRename, totalParsed, parsed, rejectFormula]
      rw [output, reject_bits_length]
      omega
  | some formula =>
      have correct := BinaryParsing.decodeFormula_sound input formula parsed
      have bound := BinaryOccurrenceRename.renamed_encoding_bound_bits formula
      simp only [totalRename, totalParsed, parsed, Option.getD_some]
      rw [correct]
      omega

end MaxCutGames.BinaryLanguage

namespace MaxCutGames.Explicit.MachineOutputContract

open MaxCutGames.Foundations
open Target
open scoped BigOperators

/-- A canonical orientation from the false side to the true side. Injectivity
is on occurrence indices, so two distinct list entries cannot be parallel even
when their constraint tables are different. -/
structure SimpleBipartite {q : Nat} (game : Instance q) where
  side : Fin game.vertices → Bool
  sourceSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].source = false
  targetSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].target = true
  endpoints_injective : Function.Injective (fun i : Fin game.constraints.length =>
    (game.constraints[i].source, game.constraints[i].target))

/-- The full forward and inverse tables already prove the permutation laws. -/
def permutationEquiv {q : Nat} (table : PermutationTable q) : Equiv.Perm (Fin q) where
  toFun label := table.images[label]
  invFun label := table.inverseImages[label]
  left_inv := table.leftInverse
  right_inv := table.rightInverse

namespace SimpleBipartite

variable {q : Nat} {game : Instance q} (presentation : SimpleBipartite game)

include presentation in
theorem no_loops (i : Fin game.constraints.length) :
    game.constraints[i].source ≠ game.constraints[i].target := by
  intro same
  have sides := congrArg presentation.side same
  rw [presentation.sourceSide, presentation.targetSide] at sides
  cases sides

include presentation in
theorem no_reverse (i j : Fin game.constraints.length) :
    game.constraints[i].source ≠ game.constraints[j].target := by
  intro same
  have sides := congrArg presentation.side same
  rw [presentation.sourceSide, presentation.targetSide] at sides
  cases sides

include presentation in
/-- Simplicity concerns unordered endpoint pairs, independently of how an edge
could have been presented before the canonical bipartite orientation. -/
theorem undirected_unique (i j : Fin game.constraints.length)
    (same :
      (game.constraints[i].source = game.constraints[j].source ∧
        game.constraints[i].target = game.constraints[j].target) ∨
      (game.constraints[i].source = game.constraints[j].target ∧
        game.constraints[i].target = game.constraints[j].source)) : i = j := by
  rcases same with same | reversed
  · exact presentation.endpoints_injective (Prod.ext same.1 same.2)
  · exact False.elim (presentation.no_reverse i j reversed.1)

/-- The list presentation yields exactly the bipartite occurrence abstraction
used by the v2 subdivision proof, without quotienting or discarding occurrences. -/
def toBipartiteGame : BipartiteGame
    {v : Fin game.vertices // presentation.side v = false}
    {v : Fin game.vertices // presentation.side v = true}
    (Fin game.constraints.length) (Fin q) where
  left i := ⟨game.constraints[i].source, presentation.sourceSide i⟩
  right i := ⟨game.constraints[i].target, presentation.targetSide i⟩
  permutation i := permutationEquiv game.constraints[i].permutation
  simple := by
    intro i j same
    apply presentation.endpoints_injective
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst same)
    · exact congrArg Subtype.val (congrArg Prod.snd same)

/-- Restricting one vertex labeling to the two sides preserves every individual
constraint's satisfaction predicate, hence its original occurrence identity. -/
theorem toBipartiteGame_satisfied_iff (labeling : Fin game.vertices → Fin q)
    (i : Fin game.constraints.length) :
    presentation.toBipartiteGame.Satisfied
      (fun v => labeling v.val) (fun v => labeling v.val) i ↔
      game.constraints[i].satisfied labeling = true := by
  simp [BipartiteGame.Satisfied, toBipartiteGame, permutationEquiv,
    Constraint.satisfied, eq_comm]

/-- Two independently chosen side labelings give one total labeling because
every vertex has exactly one Boolean side. Isolated vertices cause no exception. -/
def mergeLabelings
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    Fin game.vertices → Fin q := fun v =>
  if h : presentation.side v = false then left ⟨v, h⟩
  else right ⟨v, by cases hs : presentation.side v <;> simp_all⟩

@[simp] theorem mergeLabelings_left
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = false}) :
    presentation.mergeLabelings left right v.val = left v := by
  simp [mergeLabelings, v.property]

@[simp] theorem mergeLabelings_right
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = true}) :
    presentation.mergeLabelings left right v.val = right v := by
  simp [mergeLabelings, v.property]

theorem toBipartiteGame_count (labeling : Fin game.vertices → Fin q) :
    presentation.toBipartiteGame.satisfiedCount
      (fun v => labeling v.val) (fun v => labeling v.val) =
      countSatisfied labeling game.constraints := by
  have count := Integration.GapSemantics.countSatisfied_ofFn labeling
    (fun i : Fin game.constraints.length => game.constraints[i])
  simp only [Fin.getElem_fin, List.ofFn_getElem] at count
  rw [count]
  unfold BipartiteGame.satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  simp [toBipartiteGame, permutationEquiv, Constraint.satisfied]
  rfl

theorem toBipartiteGame_count_merge
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    presentation.toBipartiteGame.satisfiedCount left right =
      countSatisfied (presentation.mergeLabelings left right) game.constraints := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    presentation.toBipartiteGame_count (presentation.mergeLabelings left right)

theorem toBipartiteGame_maxSatisfied :
    presentation.toBipartiteGame.maxSatisfied =
      Integration.InstanceValue.maxSatisfied game := by
  classical
  apply Nat.le_antisymm
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [presentation.toBipartiteGame_count_merge labeling.1 labeling.2]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied _ _
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← presentation.toBipartiteGame_count labeling]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

/-- The abstract bipartite game and the actual serialized list instance have
exactly the same value, including the same denominator of edge occurrences. -/
theorem toBipartiteGame_value :
    presentation.toBipartiteGame.value = Integration.InstanceValue.value game := by
  unfold BipartiteGame.value Integration.InstanceValue.value
  rw [presentation.toBipartiteGame_maxSatisfied]
  simp

end SimpleBipartite

/-- Every parameter, coordinate identification, program, and polynomial is
fixed before the input quantifier. The identity input encoding measures runtime
in the original raw bit length, including sparse binary variable names. -/
structure BinaryGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  dimension : Nat
  dimensionPositive : 1 ≤ dimension
  coordinates : Fin alphabet ≃ Integration.BinaryLinear.Vector dimension
  construct : List Bool → Instance alphabet
  simpleBipartite : ∀ input, SimpleBipartite (construct input)
  translations : ∀ input,
    Integration.TranslationTarget.IsTranslationInstance coordinates (construct input)
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    Complexity.gameBits construct
  finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ input, BinaryLanguage.language input →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (construct input).constraints : ℝ) /
        (construct input).constraints.length
  soundness : ∀ input, ¬BinaryLanguage.language input →
    ∀ labeling, (countSatisfied labeling (construct input).constraints : ℝ) /
      (construct input).constraints.length ≤ δ

namespace BinaryGapReduction

variable {ε δ : ℝ} (reduction : BinaryGapReduction ε δ)

theorem nonempty (input : List Bool) : (reduction.construct input).constraints ≠ [] :=
  (reduction.construct input).nonempty

theorem occurrence_count_positive (input : List Bool) :
    0 < (reduction.construct input).constraints.length :=
  (reduction.construct input).constraintCount_positive

theorem completeness_value (input : List Bool) (yes : BinaryLanguage.language input) :
    1 - ε ≤ Integration.InstanceValue.value (reduction.construct input) := by
  have positive : 0 < reduction.alphabet :=
    lt_of_lt_of_le (by decide : 0 < 2) reduction.alphabetAtLeastTwo
  exact (Integration.InstanceValue.exists_rate_ge_iff _ positive _).mp
    (reduction.completeness input yes)

theorem soundness_value (input : List Bool) (no : ¬BinaryLanguage.language input) :
    Integration.InstanceValue.value (reduction.construct input) ≤ δ := by
  have positive : 0 < reduction.alphabet :=
    lt_of_lt_of_le (by decide : 0 < 2) reduction.alphabetAtLeastTwo
  exact (Integration.InstanceValue.forall_rate_le_iff _ positive _).mp
    (reduction.soundness input no)

/-- The fixed coordinate equivalence forces the explicit table alphabet to
have exactly the requested binary-vector cardinality. -/
theorem alphabet_eq_two_pow : reduction.alphabet = 2 ^ reduction.dimension := by
  have cardinal := Fintype.card_congr reduction.coordinates
  simpa [Integration.BinaryLinear.Vector] using cardinal

theorem no_loops (input : List Bool)
    (i : Fin (reduction.construct input).constraints.length) :
    (reduction.construct input).constraints[i].source ≠
      (reduction.construct input).constraints[i].target :=
  (reduction.simpleBipartite input).no_loops i

theorem undirected_unique (input : List Bool)
    (i j : Fin (reduction.construct input).constraints.length)
    (same :
      ((reduction.construct input).constraints[i].source =
          (reduction.construct input).constraints[j].source ∧
        (reduction.construct input).constraints[i].target =
          (reduction.construct input).constraints[j].target) ∨
      ((reduction.construct input).constraints[i].source =
          (reduction.construct input).constraints[j].target ∧
        (reduction.construct input).constraints[i].target =
          (reduction.construct input).constraints[j].source)) : i = j :=
  (reduction.simpleBipartite input).undirected_unique i j same

/-- Every occurrence serializes all forward-table entries, not an oracle or
an intensional description of the constraint. -/
theorem full_table_length (input : List Bool)
    (i : Fin (reduction.construct input).constraints.length) :
    (Complexity.tableWords
      (reduction.construct input).constraints[i].permutation).length = reduction.alphabet :=
  Complexity.tableWords_length _

theorem translation_equation (input : List Bool)
    (i : Fin (reduction.construct input).constraints.length) :
    ∃ shift : Integration.BinaryLinear.Vector reduction.dimension,
      ∀ label : Fin reduction.alphabet,
        reduction.coordinates
            ((reduction.construct input).constraints[i].permutation.images[label]) =
          reduction.coordinates label + shift :=
  reduction.translations input _ (List.getElem_mem i.isLt)

/-- The machine's exact output bits decode to the same ordered occurrence list,
with the same endpoints and all the same permutation tables. -/
theorem decode_output (input : List Bool) :
    Complexity.decodeGameBits reduction.alphabet
      (Complexity.gameBits (reduction.construct input)) =
        some (reduction.construct input) :=
  Complexity.decodeGameBits_encoded _

theorem output_word_count (input : List Bool) :
    (Complexity.gameWords (reduction.construct input)).length =
      3 + (reduction.construct input).constraints.length * (reduction.alphabet + 2) :=
  Complexity.gameWords_length _

/-- Malformed words are in the NO language and are processed by the same fixed
machine; they do not need an extra promised-input condition. -/
theorem malformed_soundness (input : List Bool)
    (malformed : BinaryEncoding.decodeFormula input = none) :
    ∀ labeling, (countSatisfied labeling (reduction.construct input).constraints : ℝ) /
      (reduction.construct input).constraints.length ≤ δ := by
  apply reduction.soundness input
  rintro ⟨formula, decoded, _⟩
  rw [malformed] at decoded
  cases decoded

end BinaryGapReduction
end MaxCutGames.Explicit.MachineOutputContract

end OAI
