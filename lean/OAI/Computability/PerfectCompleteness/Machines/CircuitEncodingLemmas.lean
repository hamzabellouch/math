import OAI.Computability.PerfectCompleteness.Machines.CircuitLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin

open CircuitProducerModel

def gateRecord (output : Nat) : Gate → Record
  | .const false => ⟨0, output, 0, 0⟩
  | .const true => ⟨1, output, 0, 0⟩
  | .not a => ⟨2, output, a, 0⟩
  | .and a b => ⟨3, output, a, b⟩
  | .or a b => ⟨4, output, a, b⟩

def gateRecords (start : Nat) : List Gate → List Record
  | [] => []
  | g :: gs => gateRecord start g :: gateRecords (start + 1) gs

def Circuit.records (C : Circuit) : List Record := gateRecords C.inputs C.gates

def recordsWords (rs : List Record) : List Nat := rs.flatMap Record.words
def recordsBits (rs : List Record) : List Bool := encodeWords (recordsWords rs)

def circuitWords (C : Circuit) : List Nat :=
  [C.wires, C.gates.length, C.output.val] ++ recordsWords C.records

def circuitBits (C : Circuit) : List Bool := encodeWords (circuitWords C)

@[simp] theorem gateRecords_length (start : Nat) (gs : List Gate) :
    (gateRecords start gs).length = gs.length := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih => simp [gateRecords, ih]

@[simp] theorem Circuit.records_length (C : Circuit) : C.records.length = C.gates.length :=
  gateRecords_length C.inputs C.gates

@[simp] theorem recordsWords_cons (r : Record) (rs : List Record) :
    recordsWords (r :: rs) = r.words ++ recordsWords rs := rfl

@[simp] theorem recordsBits_cons (r : Record) (rs : List Record) :
    recordsBits (r :: rs) = r.bits ++ recordsBits rs := by
  simp [recordsBits, Record.bits]

@[simp] theorem recordsWords_length (rs : List Record) :
    (recordsWords rs).length = 4 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [recordsWords_cons, List.length_append, ih]
      simp only [Record.words, List.length_cons, List.length_nil]
      omega

@[simp] theorem circuitWords_length (C : Circuit) :
    (circuitWords C).length = 3 + 4 * C.gates.length := by
  simp [circuitWords]
  omega

def gateFromFields (tag first second : Nat) : Gate :=
  match tag with
  | 0 => .const false
  | 1 => .const true
  | 2 => .not first
  | 3 => .and first second
  | _ => .or first second

def decodeGateWords : List Nat → List Gate
  | tag :: _ :: first :: second :: rest =>
      gateFromFields tag first second :: decodeGateWords rest
  | _ => []

theorem decodeGateWords_gateRecord (output : Nat) (g : Gate) (rest : List Nat) :
    decodeGateWords ((gateRecord output g).words ++ rest) =
      g :: decodeGateWords rest := by
  cases g with
  | const b => cases b <;> rfl
  | not a => rfl
  | and a b => rfl
  | or a b => rfl

@[simp] theorem decodeGateWords_gateRecords (start : Nat) (gs : List Gate) :
    decodeGateWords (recordsWords (gateRecords start gs)) = gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
      rw [gateRecords, recordsWords_cons, decodeGateWords_gateRecord, ih]

theorem circuitWords_injective : Function.Injective circuitWords := by
  intro C D h
  have hh : C.wires = D.wires ∧ C.gates.length = D.gates.length ∧
      C.output.val = D.output.val ∧ recordsWords C.records = recordsWords D.records := by
    simpa only [circuitWords, List.cons_append, List.nil_append, List.cons.injEq] using h
  have hg : C.gates = D.gates := by
    have hd := congrArg decodeGateWords hh.2.2.2
    simpa only [Circuit.records, decodeGateWords_gateRecords] using hd
  have hi : C.inputs = D.inputs := by
    have hw := hh.1
    simp only [Circuit.wires] at hw
    rw [hg] at hw
    omega
  cases C with
  | mk ci cg co cx =>
    cases D with
    | mk di dg dord dx =>
      dsimp at hi hg hh
      subst di
      subst dg
      have hx : cx = dx := Fin.ext hh.2.2.1
      subst dx
      rfl

theorem circuitBits_injective : Function.Injective circuitBits := by
  intro C D h
  exact circuitWords_injective (encodeWords_injective h)

theorem gateRecord_fields_le (start bound : Nat) (g : Gate)
    (hs : start ≤ bound) (hg : g.Bounded bound) :
    ∀ n ∈ (gateRecord start g).words, n ≤ bound + 4 := by
  cases g with
  | const b => cases b <;> simp [gateRecord, Record.words] <;> omega
  | not a => simp [gateRecord, Record.words, Gate.Bounded] at *; omega
  | and a b => simp [gateRecord, Record.words, Gate.Bounded] at *; omega
  | or a b => simp [gateRecord, Record.words, Gate.Bounded] at *; omega

theorem gateRecords_fields_le (start : Nat) (gs : List Gate) (ho : Ordered start gs) :
    ∀ n ∈ recordsWords (gateRecords start gs), n ≤ start + gs.length + 4 := by
  induction gs generalizing start with
  | nil => simp [gateRecords, recordsWords]
  | cons g gs ih =>
      rcases (ordered_cons start g gs).mp ho with ⟨hg, hgs⟩
      intro n hn
      rw [gateRecords, recordsWords_cons, List.mem_append] at hn
      rcases hn with hn | hn
      · have h := gateRecord_fields_le start start g (Nat.le_refl _) hg n hn
        simp only [List.length_cons]
        omega
      · have h := ih (start + 1) hgs n hn
        simp only [List.length_cons]
        omega

theorem circuitWords_bounded (C : Circuit) :
    ∀ n ∈ circuitWords C, n ≤ C.wires + 4 := by
  intro n hn
  simp only [circuitWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with (rfl | rfl | rfl) | hn
  · omega
  · simp only [Circuit.wires]; omega
  · have := C.output.isLt
    change C.output.val ≤ C.inputs + C.gates.length + 4
    omega
  · exact gateRecords_fields_le C.inputs C.gates C.ordered n hn

theorem circuitBits_length_le (C : Circuit) :
    (circuitBits C).length ≤ (3 + 4 * C.gates.length) * (C.wires + 5) := by
  have h := encodeWords_length_le (circuitWords C) (C.wires + 4)
    (circuitWords_bounded C)
  simpa only [circuitBits, circuitWords_length, Nat.add_assoc] using h

theorem circuit_header_le_length (C : Circuit) :
    C.wires + C.gates.length + C.output.val + 3 ≤ (circuitBits C).length := by
  simp only [circuitBits, circuitWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Foundations.Complexity.CookLevin

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin

open Target CircuitProducerModel

theorem gateClauses_words {n : Nat} (output : Fin n) (g : Gate) (h : g.Bounded n) :
    (gateClauses output g h).flatMap clauseWords = (gateRecord output.val g).outputWords := by
  cases g with
  | const b => cases b <;> rfl
  | not x => rfl
  | and x y => rfl
  | or x y => rfl

@[simp] theorem unitClause_words {n : Nat} (output : Fin n) :
    clauseWords (unitClause output true) = outputWords output.val := rfl

theorem gateRecords_outputWords (start : Nat) (gs : List Gate) :
    (List.finRange gs.length).flatMap
        (fun i => (gateRecord (start + i.val) gs[i.val]).outputWords) =
      (gateRecords start gs).flatMap Record.outputWords := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    change (List.finRange (gs.length + 1)).flatMap
      (fun i => (gateRecord (start + i.val) (g :: gs)[i.val]).outputWords) = _
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    change (gateRecord start g).outputWords ++
        (List.finRange gs.length).flatMap
          (fun i => (gateRecord (start + (i.val + 1)) gs[i.val]).outputWords) =
      (gateRecord start g).outputWords ++
        (gateRecords (start + 1) gs).flatMap Record.outputWords
    apply congrArg ((gateRecord start g).outputWords ++ ·)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1)

theorem Circuit.gateBlocks_words (C : Circuit) :
    ((List.finRange C.gates.length).flatMap C.gateBlock).flatMap clauseWords =
      C.records.flatMap Record.outputWords := by
  rw [List.flatMap_assoc]
  calc
    _ = (List.finRange C.gates.length).flatMap
        (fun i => (gateRecord (C.inputs + i.val) C.gates[i.val]).outputWords) := by
      apply List.flatMap_congr
      intro i _
      exact gateClauses_words (C.gateOutput i) (C.gateAt i) (C.gateBounded i)
    _ = C.records.flatMap Record.outputWords := gateRecords_outputWords C.inputs C.gates

theorem Circuit.formulaWords_eq_records (C : Circuit) :
    formulaWords C.toFormula =
      [C.wires, 3 * C.gates.length + 1] ++
        C.records.flatMap Record.outputWords ++ outputWords C.output.val := by
  unfold formulaWords
  change [C.wires, C.toFormula.clauses.length] ++ C.toFormula.clauses.flatMap clauseWords = _
  rw [C.toFormula_clause_count]
  change [C.wires, 3 * C.gates.length + 1] ++
      (((List.finRange C.gates.length).flatMap C.gateBlock ++
        [unitClause C.output true]).flatMap clauseWords) = _
  rw [List.flatMap_append, C.gateBlocks_words]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, unitClause_words,
    List.append_assoc]

theorem Circuit.formulaBits_eq_records (C : Circuit) :
    formulaBits C.toFormula =
      encodeWords ([C.wires, 3 * C.gates.length + 1] ++
        C.records.flatMap Record.outputWords ++ outputWords C.output.val) :=
  congrArg encodeWords C.formulaWords_eq_records

end UniqueGamesTheorem.Foundations.Complexity.CookLevin

end

end OAI
