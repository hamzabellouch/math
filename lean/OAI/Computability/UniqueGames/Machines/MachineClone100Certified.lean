import OAI.Computability.UniqueGames.Machines.MachineClone100Run

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Certified

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity

noncomputable def timePolynomial (copies : Nat) : Polynomial Nat :=
  Polynomial.C (300 * copies) * Polynomial.X * Polynomial.X +
    Polynomial.C (120 + 18 * copies) * Polynomial.X + Polynomial.C 23

theorem timePolynomial_eval (copies length : Nat) :
    (timePolynomial copies).eval length =
      (300 * copies) * length * length + (120 + 18 * copies) * length + 23 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

private theorem numericalBudget (D N n m B out : Nat)
    (hn : n ≤ N) (hm : m ≤ N) (hB : B ≤ N)
    (ho : out ≤ (300 * D) * N * N + (100 + 3 * D) * N + 2) :
    (out + 2) + (((2 + 3 * D) * B + (9 + 12 * D) * m + 1) +
      (5 * n + 4 * m + 18)) ≤ (300 * D) * N * N + (120 + 18 * D) * N + 23 := by
  have hn' := Nat.mul_le_mul_left 5 hn
  have hm' := Nat.mul_le_mul_left (13 + 12 * D) hm
  have hb' := Nat.mul_le_mul_left (2 + 3 * D) hB
  calc
    _ = 5 * n + (13 + 12 * D) * m + (2 + 3 * D) * B + out + 21 := by ring
    _ ≤ 5 * N + (13 + 12 * D) * N + (2 + 3 * D) * N +
        ((300 * D) * N * N + (100 + 3 * D) * N + 2) + 21 := by omega
    _ = _ := by ring

noncomputable def certifiedFunction (triples : List (CloneGap.Index × CloneGap.Index × CloneGap.Index))
    (nonempty : triples ≠ []) (f : SourceEncoding.Input → SourceEncoding.Input)
    (output_eq : ∀ input, SourceEncoding.inputBits (f input) =
      MachineClone100Run.outputBits triples input)
    (size_bound : ∀ input,
      (SourceEncoding.inputBits (f input)).length ≤
        (300 * triples.length) * (SourceEncoding.inputBits input).length *
            (SourceEncoding.inputBits input).length +
          (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2) :
    TM2ComputableInPolyTime SourceEncoding.inputBits SourceEncoding.inputBits f where
  tm := MachineClone100Run.tm triples nonempty
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial triples.length
  outputsFun input := by
    change TM2OutputsInTime (MachineClone100Run.tm triples nonempty)
      ((SourceEncoding.inputBits input).map id)
      (some ((SourceEncoding.inputBits (f input)).map id))
      ((timePolynomial triples.length).eval (SourceEncoding.inputBits input).length)
    rw [@List.map_id ((MachineClone100Run.tm triples nonempty).Γ
      (MachineClone100Run.tm triples nonempty).k₀) (SourceEncoding.inputBits input),
      @List.map_id ((MachineClone100Run.tm triples nonempty).Γ
        (MachineClone100Run.tm triples nonempty).k₁) (SourceEncoding.inputBits (f input)),
      output_eq input, timePolynomial_eval]
    let actual := MachineClone100Run.runInTime triples nonempty input
    refine { toEvalsTo := actual.toEvalsTo, steps_le_m := actual.steps_le_m.trans ?_ }
    apply numericalBudget
    · exact SourceEncoding.inputBits_length_ge_variables input
    · exact SourceEncoding.inputBits_length_ge_equations input
    · have h := SourceEncoding.inputBits_length input
      change (SourceEncoding.inputBits input).length =
        input.variables + input.equations.length + 2 +
          (MachineClone100Run.sourceBody input).length at h
      omega
    · rw [← output_eq input]
      exact size_bound input

end UniqueGamesTheorem.Explicit.MachineClone100Certified

end

end OAI
