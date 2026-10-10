import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.SourceOccurrences
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressArithmetic

open scoped BigOperators
open Target SourceContexts SourceOccurrences

theorem variable_rank (F : Formula) (u : ℕ) (v : VariableContext F u) :
    ((variableEncoding F u).code v).val =
      ∑ t : Fin u, (v t).val * F.variables ^ t.val := rfl

theorem clause_rank (F : Formula) (u : ℕ) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val =
      ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val := rfl

theorem left_address (F : Formula) (u : ℕ) (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ((variableEncoding F u).code v).val := rfl

theorem right_address (F : Formula) (u : ℕ) (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.variables ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val) := rfl

theorem dummy_address (F : Formula) (u : ℕ) :
    (dummyIndex F u).val =
      F.variables ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u) := by
  change F.variables ^ u * 2 ^ (2 ^ u) +
    (F.clauses.length ^ u * 2 ^ (8 ^ u) + 0) = _
  omega

theorem left_address_radix (F : Formula) (u : ℕ)
    (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ∑ t : Fin u, (v t).val * F.variables ^ t.val := by
  rw [left_address, variable_rank]

theorem right_address_radix (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.variables ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val) := by
  rw [right_address, clause_rank]

theorem nBits_eq_dummy_succ (F : Formula) (u : ℕ) :
    nBits F u = (dummyIndex F u).val + 1 := by
  rw [dummy_address, nBits_eq]
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceAddressArithmetic

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBounds

open Target
open UniqueGamesTheorem.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.variables + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_variables (F : Formula) :
    F.variables ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_clauses (F : Formula) :
    F.clauses.length ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_two (F : Formula) :
    2 ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

/-- The two padded long-code tables and one global dummy bit. -/
def bitCountFormula (n m u : ℕ) : ℕ :=
  n ^ u * 2 ^ (2 ^ u) + m ^ u * 2 ^ (8 ^ u) + 1

/-- Depends on the fixed repetition count alone. -/
def bitCoefficient (u : ℕ) : ℕ := 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1

/-- The slot tuples, two queries, and noise tapes per clause tuple.
The empty-context branch uses the global dummy and adds no random tape. -/
def testCoefficient (u D : ℕ) : ℕ :=
  3 ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u)

/-- The total encoding also handles an empty formula with one dummy equation. -/
def occurrenceCoefficient (u D : ℕ) : ℕ := testCoefficient u D + 1

theorem one_le_input_power (F : Formula) (u : ℕ) :
    1 ≤ (Complexity.formulaBits F).length ^ u := by
  apply Nat.one_le_pow
  have h := formulaBits_length_ge_two F
  omega

theorem bitCountFormula_le_input (F : Formula) (u : ℕ) :
    bitCountFormula F.variables F.clauses.length u ≤
      bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have hn := Nat.pow_le_pow_left (formulaBits_length_ge_variables F) u
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  have hpos := one_le_input_power F u
  unfold bitCountFormula bitCoefficient
  calc
    _ ≤ (Complexity.formulaBits F).length ^ u * 2 ^ (2 ^ u) +
        (Complexity.formulaBits F).length ^ u * 2 ^ (8 ^ u) +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.mul_le_mul_right _ hm)) hpos
    _ = _ := by ring

theorem testCountFormula_le_input (F : Formula) (u D : ℕ) :
    (F.clauses.length * 3) ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u) ≤
      testCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  calc
    _ = testCoefficient u D * F.clauses.length ^ u := by
      simp only [testCoefficient, Nat.mul_pow]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ hm

theorem testCountFormula_add_one_le_input (F : Formula) (u D : ℕ) :
    (F.clauses.length * 3) ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u) + 1 ≤
      occurrenceCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  calc
    _ ≤ testCoefficient u D * (Complexity.formulaBits F).length ^ u +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add (testCountFormula_le_input F u D) (one_le_input_power F u)
    _ = _ := by simp only [occurrenceCoefficient, Nat.add_mul, Nat.one_mul]

def sourceSizeBound (V E u L : ℕ) : ℕ :=
  V * L ^ u + E * L ^ u + 2 + E * L ^ u * (3 * (V * L ^ u) + 2)

theorem sourceBits_length_le (input : SourceEncoding.Input) (V E u L : ℕ)
    (hv : input.variables ≤ V * L ^ u)
    (he : input.equations.length ≤ E * L ^ u) :
    (SourceEncoding.inputBits input).length ≤ sourceSizeBound V E u L := by
  apply (SourceEncoding.inputBits_length_le input).trans
  unfold sourceSizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hv he) 2)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hv) 2))

/-- One explicit output-length polynomial for each fixed `u,D`. -/
noncomputable def sourcePolynomial (u D : ℕ) : Polynomial ℕ :=
  let V := Polynomial.C (bitCoefficient u) * Polynomial.X ^ u
  let E := Polynomial.C (occurrenceCoefficient u D) * Polynomial.X ^ u
  V + E + Polynomial.C 2 + E * (Polynomial.C 3 * V + Polynomial.C 2)

theorem sourcePolynomial_eval (u D L : ℕ) :
    (sourcePolynomial u D).eval L =
      sourceSizeBound (bitCoefficient u) (occurrenceCoefficient u D) u L := by
  simp [sourcePolynomial, sourceSizeBound]

open SourceOccurrences SourceContexts

/-- Exact cardinality of the actual fixed query/noise tape. -/
theorem card_testTape (u D : ℕ) :
    Fintype.card (SourceTape.TestTape (I u) (J u) D) =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := by
  rw [SourceTape.card_testTape, card_I, card_J]

/-- The executable radix enumeration has the same fixed size. -/
theorem testTapeEncoding_size (u D : ℕ) :
    (SourceOccurrences.testTapeEncoding u D).size =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := rfl

/-- Cardinality of the actual complete random-tape population. -/
theorem card_sourceIndex (F : Formula) (u D : ℕ) :
    Fintype.card (SourceIndex F u D) =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [(sourceIndexEncoding F u D).card_eq_size]
  rfl

/-- Bound on the actual variable count, including padded addresses and dummy. -/
theorem nBits_le_input (F : Formula) (u : ℕ) :
    nBits F u ≤ bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have h := bitCountFormula_le_input F u
  simpa only [nBits_eq, bitCountFormula, Nat.add_assoc] using h

/-- Exact list size retains every repeated sampled context and equation. -/
theorem rawSourceList_length_eq (F : Formula) (u D : ℕ) :
    (rawSourceList F u D).length = testCoefficient u D * F.clauses.length ^ u := by
  rw [rawSourceList_length]
  unfold testCoefficient
  ac_rfl

theorem rawSourceList_length_le_input (F : Formula) (u D : ℕ) :
    (rawSourceList F u D).length ≤
      testCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  rw [rawSourceList_length_eq]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u)

/-- Bound on the total actual list, also covering the empty-formula branch. -/
theorem sourceList_length_le_input (F : Formula) (u D : ℕ) :
    (sourceList F u D).length ≤
      occurrenceCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  calc
    _ ≤ (rawSourceList F u D).length + 1 := sourceList_length_le_raw_add_one F u D
    _ ≤ testCoefficient u D * (Complexity.formulaBits F).length ^ u +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add (rawSourceList_length_le_input F u D) (one_le_input_power F u)
    _ = _ := by simp only [occurrenceCoefficient, Nat.add_mul, Nat.one_mul]

theorem sourceInput_bits_polynomial (F : Formula) (u D : ℕ) (hD : 0 < D) :
    (SourceEncoding.inputBits (sourceInput F u D hD)).length ≤
      (sourcePolynomial u D).eval (Complexity.formulaBits F).length := by
  rw [sourcePolynomial_eval]
  exact sourceBits_length_le (sourceInput F u D hD)
    (bitCoefficient u) (occurrenceCoefficient u D) u (Complexity.formulaBits F).length
    (nBits_le_input F u) (sourceList_length_le_input F u D)

/-- Fixed parameters supply one polynomial uniformly for all actual inputs. -/
theorem fixed_parameters_source_size (u D : ℕ) (hD : 0 < D) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (sourceInput F u D hD)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  ⟨sourcePolynomial u D, fun F => sourceInput_bits_polynomial F u D hD⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceBounds

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

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

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

namespace UniqueGamesTheorem.Foundations.Hastad.SourceEnumeration

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
    (emit : UniqueGamesTheorem.Reduction.CloneGap.Equation (Fin (nBits F u)) → List α) :
    (rawSourceList F u D).flatMap emit =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.flatMap
                (fun g => emit (contextEquation F u D c (sampledVariables F c s) (f, z, g))))))) := by
  rw [rawSourceList_eq_nestedLoops]
  simp only [List.flatMap_assoc, List.flatMap_map]

end UniqueGamesTheorem.Foundations.Hastad.SourceEnumeration

end

end OAI
