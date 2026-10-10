import OAI.Computability.UniqueGames.Machines.MachineClone100Certified
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.PCP.Clone100

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations.Complexity

noncomputable section

def indices (t : Outer.Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

def triples : List (Nat × Nat × Nat) := Outer.Clone100.triples.map indices

theorem triples_length : triples.length = 970200 := by
  simp [triples, Outer.Clone100.triples_length]

theorem triples_nonempty : triples ≠ [] := by
  apply List.length_pos_iff.mp
  rw [triples_length]
  decide

theorem equation_words {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Outer.Clone100Triples.GoodTriple) :
    SourceEncoding.equationWords (Outer.Clone100.equation e t) =
      MachineClone100Table.cloneEquationWords e (indices t) := by
  simp [SourceEncoding.equationWords, Outer.Clone100.equation,
    Outer.Clone100.nameEquiv, finProdFinEquiv,
    MachineClone100Table.cloneEquationWords, indices, Nat.mul_comm]

theorem body_words {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    (Outer.Clone100.equations es).flatMap SourceEncoding.equationWords =
      es.flatMap (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [Outer.Clone100.equations, List.flatMap_assoc, List.flatMap_map,
    equation_words, triples]

theorem input_words_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (Outer.Clone100.clonedInput input) =
      [100 * input.variables, triples.length * input.equations.length] ++
        input.equations.flatMap
          (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [SourceEncoding.inputWords, Outer.Clone100.clonedInput,
    Outer.Clone100.equations_length, body_words, triples_length]
  simp [Nat.mul_comm]

theorem input_bits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits (Outer.Clone100.clonedInput input) =
      MachineClone100Run.outputBits triples input := by
  rw [SourceEncoding.inputBits, input_words_eq, encodeWords_append]
  rfl

private theorem serialized_polynomial (D N n m : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * 100 + m * D + 2 + m * D * (300 * n + 2) ≤
      (300 * D) * N * N + (100 + 3 * D) * N + 2 := by
  have hproduct := Nat.mul_le_mul_left (300 * D) (Nat.mul_le_mul hm hn)
  have hvariables := Nat.mul_le_mul_left 100 hn
  have hoccurrences := Nat.mul_le_mul_left (3 * D) hm
  calc
    _ = (300 * D) * (m * n) + 100 * n + (3 * D) * m + 2 := by ring
    _ ≤ (300 * D) * (N * N) + 100 * N + (3 * D) * N + 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hproduct hvariables) hoccurrences)
        (Nat.le_refl 2)
    _ = _ := by ring

theorem size_bound (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (Outer.Clone100.clonedInput input)).length ≤
      (300 * triples.length) * (SourceEncoding.inputBits input).length *
        (SourceEncoding.inputBits input).length +
      (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2 := by
  rw [triples_length]
  exact (Outer.Clone100.clonedInput_bits_length_le input).trans
    (serialized_polynomial 970200 (SourceEncoding.inputBits input).length
      input.variables input.equations.length
      (SourceEncoding.inputBits_length_ge_variables input)
      (SourceEncoding.inputBits_length_ge_equations input))

def computation : TM2ComputableInPolyTime SourceEncoding.inputBits
    SourceEncoding.inputBits Outer.Clone100.clonedInput :=
  MachineClone100Certified.certifiedFunction triples triples_nonempty
    Outer.Clone100.clonedInput input_bits_eq size_bound

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

def fullRunInTime (input : SourceEncoding.Input) := computation.outputsFun input

end

end UniqueGamesTheorem.Explicit.MachineClone100

end

end OAI
