import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Hardness.LiteralSlotGraphEnumeration

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

theorem literal_variable_add_two_le_bits (literal : RawLiteral) :
    literal.1 + 2 ≤ (literalBits literal).length := by
  simp only [literalBits, List.length_append, encodeWord_length]
  omega

theorem two_mul_length_le_literalsBits_length (xs : List RawLiteral) :
    2 * xs.length ≤ (literalsBits xs).length := by
  induction xs with
  | nil => simp [literalsBits]
  | cons literal rest ih =>
      have hl := literal_variable_add_two_le_bits literal
      simp only [literalsBits_cons, List.length_append, List.length_cons]
      omega

theorem literal_bits_length_le_literalsBits {literal : RawLiteral}
    {xs : List RawLiteral} (h : literal ∈ xs) :
    (literalBits literal).length ≤ (literalsBits xs).length := by
  induction xs with
  | nil => simp at h
  | cons head rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst literal
        simp only [literalsBits_cons, List.length_append]
        omega
      · have ht := ih h
        simp only [literalsBits_cons, List.length_append]
        omega

theorem literal_variable_le_literalsBits {literal : RawLiteral}
    {xs : List RawLiteral} (h : literal ∈ xs) :
    literal.1 ≤ (literalsBits xs).length := by
  have h₁ := literal_variable_add_two_le_bits literal
  have h₂ := literal_bits_length_le_literalsBits h
  omega

theorem literalsBits_formula_length_le (F : Formula) :
    (literalsBits (formulaLiterals F)).length ≤ (formulaBits F).length := by
  rw [formulaBits_eq_formulaLiterals]
  simp only [List.length_append]
  omega

theorem formula_literal_variable_le_input (F : Formula) {literal : RawLiteral}
    (h : literal ∈ formulaLiterals F) :
    literal.1 ≤ (formulaBits F).length :=
  (literal_variable_le_literalsBits h).trans (literalsBits_formula_length_le F)

theorem natBits_length_le_unary (n : Nat) :
    (BinaryEncoding.natBits n).length ≤ 2 * n + 1 := by
  have hb := bits_length_le n
  rw [Nat.size_eq_bits_len] at hb
  rw [BinaryEncoding.natBits_length]
  omega

theorem pairRecord_length_le (u v B : Nat) (hu : u ≤ B) (hv : v ≤ B) :
    (pairRecord u v).length ≤ 4 * B + 3 := by
  have h₁ := natBits_length_le_unary u
  have h₂ := natBits_length_le_unary v
  simp only [pairRecord, List.length_cons, List.length_append]
  omega

theorem vertexRecord_length_le (i B : Nat) (hi : i ≤ B) :
    (vertexRecord i).length ≤ 2 * B + 2 := by
  have h := natBits_length_le_unary i
  simp only [vertexRecord, List.length_cons]
  omega

theorem vertexRecords_length_le (i n B : Nat) (h : i + n ≤ B) :
    (vertexRecords i n).length ≤ n * (2 * B + 2) := by
  induction n generalizing i with
  | zero => simp [vertexRecords]
  | succ n ih =>
      have hi := vertexRecord_length_le i B (by omega)
      have ht := ih (i + 1) (by omega)
      simp only [vertexRecords, List.length_append]
      nlinarith

theorem rowEdges_length_le (u v : Nat) (left : RawLiteral) (xs : List RawLiteral) :
    (rowEdges u v left xs).length ≤ xs.length := by
  induction xs generalizing v with
  | nil => simp [rowEdges]
  | cons right rest ih =>
      have ht := ih (v + 1)
      simp only [rowEdges]
      split_ifs <;> simp only [List.length_cons] <;> omega

theorem rowEdges_endpoint_bounds (u v : Nat) (left : RawLiteral)
    (xs : List RawLiteral) {edge : Nat × Nat} (h : edge ∈ rowEdges u v left xs) :
    edge.1 = u ∧ v ≤ edge.2 ∧ edge.2 < v + xs.length := by
  induction xs generalizing v with
  | nil => simp [rowEdges] at h
  | cons right rest ih =>
      simp only [rowEdges] at h
      split_ifs at h with hc
      · rcases List.mem_cons.mp h with he | he
        · subst edge
          simp only [List.length_cons]
          exact ⟨True.intro, le_rfl, by omega⟩
        · obtain ⟨hu, hv, ht⟩ := ih (v + 1) he
          simp only [List.length_cons]
          exact ⟨hu, by omega, by omega⟩
      · obtain ⟨hu, hv, ht⟩ := ih (v + 1) h
        simp only [List.length_cons]
        exact ⟨hu, by omega, by omega⟩

theorem suffixEdges_endpoint_bounds (u : Nat) (xs : List RawLiteral)
    {edge : Nat × Nat} (h : edge ∈ suffixEdges u xs) :
    u ≤ edge.1 ∧ edge.1 < edge.2 ∧ edge.2 < u + xs.length := by
  induction xs generalizing u with
  | nil => simp [suffixEdges] at h
  | cons literal rest ih =>
      simp only [suffixEdges, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨hu, hv, ht⟩ := rowEdges_endpoint_bounds u (u + 1) literal rest h
        simp only [List.length_cons]
        exact ⟨by omega, by omega, by omega⟩
      · obtain ⟨hu, hv, ht⟩ := ih (u + 1) h
        simp only [List.length_cons]
        exact ⟨by omega, hv, by omega⟩

theorem suffixEdges_length_le_sq (u : Nat) (xs : List RawLiteral) :
    (suffixEdges u xs).length ≤ xs.length ^ 2 := by
  induction xs generalizing u with
  | nil => simp [suffixEdges]
  | cons literal rest ih =>
      have hr := rowEdges_length_le u (u + 1) literal rest
      have ht := ih (u + 1)
      simp only [suffixEdges, List.length_append, List.length_cons]
      nlinarith

theorem edgeRecords_length_le (edges : List (Nat × Nat)) (B : Nat)
    (bounded : ∀ edge ∈ edges, edge.1 ≤ B ∧ edge.2 ≤ B) :
    (edgeRecords edges).length ≤ edges.length * (4 * B + 3) := by
  induction edges with
  | nil => simp [edgeRecords]
  | cons edge rest ih =>
      have he := bounded edge (by simp)
      have hp := pairRecord_length_le edge.1 edge.2 B he.1 he.2
      have ht := ih (fun e he => bounded e (by simp [he]))
      simp only [edgeRecords, List.flatMap_cons, List.length_append, List.length_cons]
      change (pairRecord edge.1 edge.2).length + (edgeRecords rest).length ≤ _
      nlinarith

theorem rowEdgeRecords_length_le (u v : Nat) (left : RawLiteral)
    (xs : List RawLiteral) (B : Nat) (hu : u ≤ B) (hv : v + xs.length ≤ B) :
    (edgeRecords (rowEdges u v left xs)).length ≤ xs.length * (4 * B + 3) := by
  have he := edgeRecords_length_le (rowEdges u v left xs) B (by
    intro edge h
    obtain ⟨h₁, h₂, h₃⟩ := rowEdges_endpoint_bounds u v left xs h
    exact ⟨by omega, by omega⟩)
  exact he.trans (Nat.mul_le_mul_right _ (rowEdges_length_le u v left xs))

theorem suffixEdgeRecords_length_le (u : Nat) (xs : List RawLiteral) (B : Nat)
    (hB : u + xs.length ≤ B) :
    (edgeRecords (suffixEdges u xs)).length ≤ xs.length ^ 2 * (4 * B + 3) := by
  have he := edgeRecords_length_le (suffixEdges u xs) B (by
    intro edge h
    obtain ⟨h₁, h₂, h₃⟩ := suffixEdges_endpoint_bounds u xs h
    exact ⟨by omega, by omega⟩)
  exact he.trans (Nat.mul_le_mul_right _ (suffixEdges_length_le_sq u xs))

theorem formulaEdgeRecords_length_le (F : Formula) :
    (edgeRecords (suffixEdges 0 (formulaLiterals F))).length ≤
      (formulaBits F).length ^ 2 * (4 * (formulaBits F).length + 3) := by
  have hn : (formulaLiterals F).length ≤ (formulaBits F).length := by
    rw [formulaLiterals_length]
    exact literalSlots_le_formulaBits_length F
  have he := suffixEdgeRecords_length_le 0 (formulaLiterals F)
    (formulaBits F).length (by simpa using hn)
  have hs : (formulaLiterals F).length ^ 2 ≤ (formulaBits F).length ^ 2 := by
    nlinarith
  exact he.trans (Nat.mul_le_mul_right _ hs)

theorem formulaGraphWord_length_le (F : Formula) :
    (BinaryEncoding.natBits (2 * F.clauses.length) ++
      vertexRecords 0 (3 * F.clauses.length) ++ [false] ++
      edgeRecords (suffixEdges 0 (formulaLiterals F)) ++ [false]).length ≤
      4 * (formulaBits F).length ^ 3 + 5 * (formulaBits F).length ^ 2 +
        4 * (formulaBits F).length + 3 := by
  let s := (formulaBits F).length
  have hn : 3 * F.clauses.length ≤ s := literalSlots_le_formulaBits_length F
  have hh := natBits_length_le_unary (2 * F.clauses.length)
  have hv := vertexRecords_length_le 0 (3 * F.clauses.length) s (by omega)
  have hv' : (vertexRecords 0 (3 * F.clauses.length)).length ≤ s * (2 * s + 2) :=
    hv.trans (Nat.mul_le_mul_right _ hn)
  have he := formulaEdgeRecords_length_le F
  simp only [List.length_append, List.length_cons, List.length_nil]
  change _ ≤ 4 * s ^ 3 + 5 * s ^ 2 + 4 * s + 3
  change (edgeRecords (suffixEdges 0 (formulaLiterals F))).length ≤ s ^ 2 * (4 * s + 3) at he
  nlinarith

end

open Turing FiniteTapeProgram BinPackingGames.Foundations.Target
open BinPackingGames.Foundations.Complexity

theorem edgeRecords_listBits (edges : List (Nat × Nat)) :
    edgeRecords edges ++ [false] = BinaryEncoding.listBits
      (BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits) edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change (pairRecord edge.1 edge.2 ++ edgeRecords rest) ++ [false] = _
      rw [List.append_assoc, ih]
      rfl

theorem rawInput_formula (F : Formula) :
    rawInput F.variables F.clauses.length (formulaLiterals F) = formulaBits F :=
  (formulaBits_eq_formulaLiterals F).symm

theorem rawGraphWord_graphBits (F : NonemptyFormula) :
    rawGraphWord F.val.clauses.length (formulaLiterals F.val) = graphBits (graphInput F) := by
  have vertices : vertexRecords 0 (3 * F.val.clauses.length) ++ [false] =
      BinaryEncoding.listBits BinaryEncoding.natBits (List.range (3 * F.val.clauses.length)) := by
    simpa only [← List.range_eq_range'] using
      vertexRecords_listBits 0 (3 * F.val.clauses.length)
  have edges := edgeRecords_listBits (suffixEdges 0 (formulaLiterals F.val))
  rw [suffixEdges_formulaLiterals] at edges
  change BinaryEncoding.natBits (2 * F.val.clauses.length) ++
      vertexRecords 0 (3 * F.val.clauses.length) ++ [false] ++
      edgeRecords (suffixEdges 0 (formulaLiterals F.val)) ++ [false] = _
  rw [show BinaryEncoding.natBits (2 * F.val.clauses.length) ++
      vertexRecords 0 (3 * F.val.clauses.length) ++ [false] ++
      edgeRecords (suffixEdges 0 (formulaLiterals F.val)) ++ [false] =
      BinaryEncoding.natBits (2 * F.val.clauses.length) ++
        (vertexRecords 0 (3 * F.val.clauses.length) ++ [false]) ++
        (edgeRecords (suffixEdges 0 (formulaLiterals F.val)) ++ [false]) by
      simp only [List.append_assoc]]
  rw [vertices, edgeRecords_listBits, suffixEdges_formulaLiterals]
  rfl

theorem rawCost_formula_le (F : Formula) :
    rawCost F.variables F.clauses.length (formulaLiterals F) ≤
      100 * ((formulaBits F).length + 1) ^ 3 := by
  let s := (formulaBits F).length
  have hcount : 3 * F.clauses.length ≤ s := literalSlots_le_formulaBits_length F
  have hlits : (formulaLiterals F).length ≤ s := by
    rw [formulaLiterals_length]
    exact hcount
  have htwo : 2 * F.clauses.length ≤ s := by omega
  have hvar : F.variables ≤ s := by
    have h := congrArg List.length (formulaBits_eq_formulaLiterals F)
    simp only [List.length_append, encodeWord_length] at h
    change s = _ at h
    omega
  have hqbits := (bits_length_le (2 * F.clauses.length)).trans htwo
  have hnbits := (bits_length_le (3 * F.clauses.length)).trans hcount
  have hlbits := (bits_length_le (formulaLiterals F).length).trans hlits
  have convert := UnaryToBinaryMachine.steps_le (2 * F.clauses.length) 0
  have convertMul := Nat.mul_le_mul htwo
    (show 2 * (0 + 2 * F.clauses.length) + 3 ≤ 2 * s + 3 by omega)
  have vertices := vertexLoopCost_le (3 * F.clauses.length) 0
  have verticesMul := Nat.mul_le_mul hcount
    (show 5 * (0 + 3 * F.clauses.length) + 13 ≤ 5 * s + 13 by omega)
  have outer := outerLoopCost_le initialControl 0 s (formulaLiterals F)
    (by simpa using hlits) (literalsBits_formula_length_le F)
    (fun literal h => formula_literal_variable_le_input F h)
  have outerMul := Nat.mul_le_mul_right (40 * (s + 1) ^ 2 + 1) hlits
  have output := formulaGraphWord_length_le F
  change (rawGraphWord F.clauses.length (formulaLiterals F)).length ≤
    4 * s ^ 3 + 5 * s ^ 2 + 4 * s + 3 at output
  have coarse : rawCost F.variables F.clauses.length (formulaLiterals F) ≤
      44 * s ^ 3 + 92 * s ^ 2 + 70 * s + 21 := by
    simp only [rawCost, phaseCosts, List.sum_cons, List.sum_nil]
    nlinarith
  change _ ≤ 100 * (s + 1) ^ 3
  nlinarith [Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 2)]

def outputsInTime (F : NonemptyFormula) :
    TM2OutputsInTime machine (inputBits F) (some (graphBits (graphInput F)))
      (100 * ((inputBits F).length + 1) ^ 3) := by
  have run := program.outputsInTime Tape.input .output initialState
    (rawInput F.val.variables F.val.clauses.length (formulaLiterals F.val))
    (rawGraphWord F.val.clauses.length (formulaLiterals F.val))
    (rawCost F.val.variables F.val.clauses.length (formulaLiterals F.val))
    (100 * ((formulaBits F.val).length + 1) ^ 3)
    (raw_program_exec F.val.variables F.val.clauses.length (formulaLiterals F.val))
    (rawCost_formula_le F.val)
  simpa only [rawInput_formula, rawGraphWord_graphBits, machine, inputBits] using run

noncomputable def computation :
    TM2ComputableInPolyTime inputBits graphBits graphInput where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * (Polynomial.X + Polynomial.C 1) ^ 3
  outputsFun F := by
    change TM2OutputsInTime machine ((inputBits F).map id)
      (some ((graphBits (graphInput F)).map id))
      ((Polynomial.C 100 * (Polynomial.X + Polynomial.C 1) ^ 3 : Polynomial Nat).eval
        (inputBits F).length)
    simp only [List.map_id_fun, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (inputBits F) (some (graphBits (graphInput F)))
      (100 * ((inputBits F).length + 1) ^ 3)
    exact outputsInTime F

theorem computation_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet computation.tm := machine_finiteAlphabet

end BinPackingGap.LiteralSlotGraphMachine

end OAI
