import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Model
import OAI.Computability.UniqueGames.PCP.NameCompaction

namespace OAI


namespace PerfectCompleteness.BinaryFormula

open UniqueGamesTheorem.Foundations

def clauseNames (c : Clause) : List Nat :=
  [(c)[0].name, (c)[1].name, (c)[2].name]

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (i : Fin 3) : (c)[i].name ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Nat :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

def compactClause (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) : Target.Clause (activeNames F).length :=
  #v[compactLiteral F (c)[0] (literal_mem_active F c hc 0),
    compactLiteral F (c)[1] (literal_mem_active F c hc 1),
    compactLiteral F (c)[2] (literal_mem_active F c hc 2)]

def compactClauses (F : Formula) : List (Target.Clause (activeNames F).length) :=
  F.clauses.attach.map (fun c => compactClause F c.val c.property)

def dense (F : Formula) : Target.Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Nat) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

theorem compactIndex_injective (F : Formula) (u v : Nat)
    (hu : u ∈ activeNames F) (hv : v ∈ activeNames F)
    (h : compactIndex F u hu = compactIndex F v hv) : u = v := by
  have decoded := congrArg (decodeName F) h
  simpa only [decode_compactIndex] using decoded

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

@[simp] theorem eval_compact_restrict (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (A : Nat → Bool) :
    (compactClause F c hc).eval (restrictAssignment F A) = c.eval A := by
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F c hc).eval B = c.eval (extendAssignment F B) := by
  have h₀ : (c)[0].name ∈ activeNames F := literal_mem_active F c hc 0
  have h₁ : (c)[1].name ∈ activeNames F := literal_mem_active F c hc 1
  have h₂ : (c)[2].name ∈ activeNames F := literal_mem_active F c hc 2
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, extendAssignment, h₀, h₁, h₂]
  rfl

def evaluationList (F : Formula) (A : Nat → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

theorem evaluationList_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.evaluationList (dense F) (restrictAssignment F A) =
      evaluationList F A := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  simpa only [Function.comp_def, eval_compact_restrict] using
    PCP.NameCompaction.map_attach_val F.clauses (fun c => c.eval A)

theorem evaluationList_extend (F : Formula) (B : Fin (dense F).variables → Bool) :
    PCP.NameCompaction.evaluationList (dense F) B =
      evaluationList F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  change F.clauses.attach.map (fun c => (compactClause F c.val c.property).eval B) = _
  calc
    _ = F.clauses.attach.map (fun c => c.val.eval (extendAssignment F B)) := by
      apply List.map_congr_left
      intro c _
      exact eval_compact_extend F c.val c.property B
    _ = _ := PCP.NameCompaction.map_attach_val F.clauses
      (fun c => c.eval (extendAssignment F B))

def failedCount (F : Formula) (A : Nat → Bool) : Nat :=
  (evaluationList F A).count false

theorem failedCount_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.failedCount (dense F) (restrictAssignment F A) = failedCount F A := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_restrict]

theorem failedCount_extend (F : Formula) (B : Fin (dense F).variables → Bool) :
    PCP.NameCompaction.failedCount (dense F) B = failedCount F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_extend]

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem dense_clause_count (F : Formula) :
    (dense F).clauses.length = F.clauses.length := by
  simp [dense, compactClauses]

theorem dense_variable_bound (F : Formula) :
    (dense F).variables ≤ 3 * F.clauses.length := by
  have h := PCP.NameCompaction.length_eraseDups_le (sourceNames F)
  simpa only [sourceNames, clauseNames_flat_length, dense, activeNames] using h

theorem dense_completeness (F : Formula) (hs : F.Satisfiable) :
    (dense F).Satisfiable := by
  rcases hs with ⟨A, hA⟩
  refine ⟨restrictAssignment F A, ?_⟩
  intro d hd
  change d ∈ F.clauses.attach.map (fun c => compactClause F c.val c.property) at hd
  rcases List.mem_map.mp hd with ⟨c, _, rfl⟩
  exact (eval_compact_restrict F c.val c.property A).trans (hA c.val c.property)

theorem dense_reflects (F : Formula) (hs : (dense F).Satisfiable) : F.Satisfiable := by
  rcases hs with ⟨B, hB⟩
  refine ⟨extendAssignment F B, ?_⟩
  intro c hc
  have hm : compactClause F c hc ∈ (dense F).clauses := by
    change _ ∈ F.clauses.attach.map (fun d => compactClause F d.val d.property)
    exact List.mem_map.mpr ⟨⟨c, hc⟩, by simp, rfl⟩
  rw [← eval_compact_extend F c hc B]
  exact hB _ hm

theorem dense_satisfiable_iff (F : Formula) :
    (dense F).Satisfiable ↔ F.Satisfiable :=
  ⟨dense_reflects F, dense_completeness F⟩

theorem dense_preserves_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * failedCount F A)
    (B : Fin (dense F).variables → Bool) :
    a * (dense F).clauses.length ≤ b * PCP.NameCompaction.failedCount (dense F) B := by
  rw [dense_clause_count, failedCount_extend]
  exact gap (extendAssignment F B)

theorem dense_encoding_bound (F : Formula) :
    (Complexity.formulaBits (dense F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have enc := Complexity.formulaBits_length_le (dense F)
  rw [dense_clause_count] at enc
  have active := dense_variable_bound F
  have h₁ := Nat.add_le_add_right active (F.clauses.length + 2)
  have h₂ := Nat.mul_le_mul_left F.clauses.length
    (Nat.mul_le_mul_left 3 (Nat.add_le_add_right active 2))
  have total := Nat.add_le_add h₁ h₂
  have polynomial : 3 * F.clauses.length + (F.clauses.length + 2) +
      F.clauses.length * (3 * (3 * F.clauses.length + 2)) =
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
    ring
  rw [polynomial] at total
  omega

end PerfectCompleteness.BinaryFormula



namespace PerfectCompleteness.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

def nameBits (name : Nat) : List Bool := frame name.bits

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

theorem nameBits_length_le_of_lt_pow (name width : Nat) (bound : name < 2 ^ width) :
    (nameBits name).length ≤ 2 * width + 1 := by
  rw [nameBits_length]
  have h := Nat.size_le.mpr bound
  omega

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

theorem clause_three_entries (clause : Clause) : #v[clause[0], clause[1], clause[2]] = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded (clause : Clause) (rest : List Bool) :
    parseClause (clauseBits clause ++ rest) = some (clause, rest) := by
  simp [clauseBits, List.append_assoc, parseClause, clause_three_entries]

def clauseNameSize (clause : Clause) : Nat :=
  ((clauseNames clause).map Nat.size).sum

@[simp] theorem clauseBits_length (clause : Clause) :
    (clauseBits clause).length = 2 * clauseNameSize clause + 6 := by
  simp [clauseBits, clauseNameSize, clauseNames]
  omega

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

@[simp] theorem namesBitSize_cons (clause : Clause) (clauses : List Clause) :
    namesBitSize (clause :: clauses) = clauseNameSize clause + namesBitSize clauses := by
  simp [namesBitSize, clauseNameSize]

theorem clausesBits_length (clauses : List Clause) :
    (clausesBits clauses).length = 7 * clauses.length + 2 * namesBitSize clauses + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [clausesBits, List.length_cons, List.length_append, clauseBits_length,
        namesBitSize_cons, ih]
      omega

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

theorem clauses_length_lt_bits (clauses : List Clause) :
    clauses.length < (clausesBits clauses).length := by
  rw [clausesBits_length]
  omega

def ordinarySize (formula : Formula) : Nat :=
  3 * formula.clauses.length + namesBitSize formula.clauses + 1

theorem ordinarySize_le_bits (formula : Formula) :
    ordinarySize formula ≤ (formulaBits formula).length := by
  rw [formulaBits_length]
  unfold ordinarySize
  omega

theorem bits_le_three_ordinarySize (formula : Formula) :
    (formulaBits formula).length ≤ 3 * ordinarySize formula := by
  rw [formulaBits_length]
  unfold ordinarySize
  omega

@[simp] theorem parseClauses_encoded (clauses : List Clause) (rest : List Bool)
    (fuel : Nat) (enough : clauses.length < fuel) :
    parseClauses fuel (clausesBits clauses ++ rest) = some (clauses, rest) := by
  induction clauses generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [clausesBits, parseClauses]
  | cons clause clauses ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hrest : clauses.length < fuel := by simp only [List.length_cons] at enough; omega
          simp [clausesBits, parseClauses, List.append_assoc, ih fuel hrest]

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormula same
  simpa only [decodeFormula_encoded, Option.some.injEq] using parsed

theorem dense_encoding_bound (formula : Formula) :
    (UniqueGamesTheorem.Foundations.Complexity.formulaBits (dense formula)).length ≤
      9 * (formulaBits formula).length * (formulaBits formula).length +
      10 * (formulaBits formula).length + 2 := by
  have h := BinaryFormula.dense_encoding_bound formula
  have hm : formula.clauses.length ≤ (formulaBits formula).length :=
    (clauses_length_lt_bits formula.clauses).le
  have hsq := Nat.mul_self_le_mul_self hm
  nlinarith

end PerfectCompleteness.BinaryEncoding

end OAI
