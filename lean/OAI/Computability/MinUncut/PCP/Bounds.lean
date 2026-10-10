import Mathlib
import OAI.Computability.MinUncut.PCP.Occurrences

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceBounds

open Target
open MinUncutGames.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.«variables» + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_variables (F : Formula) :
    F.«variables» ≤ (Complexity.formulaBits F).length := by
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

def bitCountFormula (n m u : ℕ) : ℕ :=
  n ^ u * 2 ^ (2 ^ u) + m ^ u * 2 ^ (8 ^ u) + 1

def bitCoefficient (u : ℕ) : ℕ := 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1

def testCoefficient (u D : ℕ) : ℕ :=
  3 ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u)

def occurrenceCoefficient (u D : ℕ) : ℕ := testCoefficient u D + 1

theorem one_le_input_power (F : Formula) (u : ℕ) :
    1 ≤ (Complexity.formulaBits F).length ^ u := by
  apply Nat.one_le_pow
  have h := formulaBits_length_ge_two F
  omega

theorem bitCountFormula_le_input (F : Formula) (u : ℕ) :
    bitCountFormula F.«variables» F.clauses.length u ≤
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
    (hv : input.«variables» ≤ V * L ^ u)
    (he : input.equations.length ≤ E * L ^ u) :
    (SourceEncoding.inputBits input).length ≤ sourceSizeBound V E u L := by
  apply (SourceEncoding.inputBits_length_le input).trans
  unfold sourceSizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hv he) 2)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hv) 2))

noncomputable def sourcePolynomial (u D : ℕ) : Polynomial ℕ :=
  let V := Polynomial.C (bitCoefficient u) * Polynomial.X ^ u
  let E := Polynomial.C (occurrenceCoefficient u D) * Polynomial.X ^ u
  V + E + Polynomial.C 2 + E * (Polynomial.C 3 * V + Polynomial.C 2)

theorem sourcePolynomial_eval (u D L : ℕ) :
    (sourcePolynomial u D).eval L =
      sourceSizeBound (bitCoefficient u) (occurrenceCoefficient u D) u L := by
  simp [sourcePolynomial, sourceSizeBound]

open SourceOccurrences SourceContexts

theorem card_testTape (u D : ℕ) :
    Fintype.card (SourceTape.TestTape (I u) (J u) D) =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := by
  rw [SourceTape.card_testTape, card_I, card_J]

theorem testTapeEncoding_size (u D : ℕ) :
    (SourceOccurrences.testTapeEncoding u D).size =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := rfl

theorem card_sourceIndex (F : Formula) (u D : ℕ) :
    Fintype.card (SourceIndex F u D) =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [(sourceIndexEncoding F u D).card_eq_size]
  rfl

theorem nBits_le_input (F : Formula) (u : ℕ) :
    nBits F u ≤ bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have h := bitCountFormula_le_input F u
  simpa only [nBits_eq, bitCountFormula, Nat.add_assoc] using h

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

theorem fixed_parameters_source_size (u D : ℕ) (hD : 0 < D) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (sourceInput F u D hD)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  ⟨sourcePolynomial u D, fun F => sourceInput_bits_polynomial F u D hD⟩

end MinUncutGames.Foundations.Hastad.SourceBounds

end

end OAI
