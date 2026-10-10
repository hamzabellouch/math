import OAI.Computability.UniqueGames.Reduction.OutputSize
import OAI.Computability.UniqueGames.Reduction.OutputTranslationsLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.AddressOutputSize

open ActualSource
open UniqueGamesTheorem.Integration
open UniqueGamesTheorem.Foundations

variable {s d : Nat}

def vertexBound (k s d inputLength : Nat) : Nat :=
  2 * ((48 + CloneGap.distinctTriples.length) * inputLength +
    2 ^ s + 2 ^ d + 4) ^ (1 + 9 * k)

def edgeBound (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) : Nat :=
  OutputSize.edgeCoefficient k T * inputLength ^ k

def bitsBound (vertices edges alphabet : Nat) : Nat :=
  vertices + alphabet + edges + 3 +
    edges * (2 * vertices + alphabet * (alphabet + 1))

theorem bitsBound_mono {vertices vertices' edges edges' alphabet : Nat}
    (hv : vertices ≤ vertices') (he : edges ≤ edges') :
    bitsBound vertices edges alphabet ≤ bitsBound vertices' edges' alphabet := by
  unfold bitsBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hv alphabet) he) 3)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) _))

def sizeBound (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) : Nat :=
  bitsBound (vertexBound k s d inputLength) (edgeBound k T inputLength) (2 ^ s)

theorem table_constraints_eq (S : Source) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints.length =
      Explicit.edgeCount S.occurrences k (s + d) T.vectors.length := by
  unfold AddressGame.tableOutput
  erw [AddressGame.outputInstance_length]
  simp only [TableReduction.tableEnumeration]
  erw [List.length_finRange]

private theorem scaled_sum_le {n m N : Nat} (a b : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * a + m * b ≤ (a + b) * N := by
  calc
    _ ≤ N * a + N * b :=
      Nat.add_le_add (Nat.mul_le_mul_right a hn) (Nat.mul_le_mul_right b hm)
    _ = _ := by rw [Nat.add_mul]; ac_rfl

private theorem collect_edge_coefficient (inputLength tripleCount iterations factor noiseCount : Nat) :
    (inputLength * tripleCount) ^ iterations * factor * noiseCount =
      (tripleCount ^ iterations * factor * noiseCount) * inputLength ^ iterations := by
  rw [Nat.mul_pow]
  ac_rfl

theorem output_constraints_eq {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (UniformReduction.source es hne) k T).constraints.length =
      edgeBound k T es.length := by
  rw [table_constraints_eq, UniformReduction.source_occurrences]
  unfold Explicit.edgeCount edgeBound OutputSize.edgeCoefficient
  exact collect_edge_coefficient _ _ _ _ _

theorem output_vertices_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T).vertices ≤
        vertexBound k s d (SourceEncoding.inputBits input).length := by
  have hn := SourceEncoding.inputBits_length_ge_variables input
  have hm := SourceEncoding.inputBits_length_ge_equations input
  have hsum := scaled_sum_le 48 CloneGap.distinctTriples.length hn hm
  change 2 * (CanonicalAddress.base
    (UniformReduction.source input.equations input.nonempty).variables
    (UniformReduction.source input.equations input.nonempty).occurrences s d) ^
      (1 + 9 * k) ≤ _
  rw [CanonicalAddress.base_eq, UniformReduction.source_variables,
    UniformReduction.source_occurrences]
  unfold vertexBound
  apply Nat.mul_le_mul_left 2
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsum _) _) _

theorem output_constraints_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T).constraints.length ≤
        edgeBound k T (SourceEncoding.inputBits input).length := by
  rw [output_constraints_eq]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (SourceEncoding.inputBits_length_ge_equations input) k)

theorem output_bits_length_le (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T)).length ≤
        sizeBound k T (SourceEncoding.inputBits input).length := by
  exact (GameEncodingSize.gameBits_length_le _).trans
    (bitsBound_mono (output_vertices_le_input input k T)
      (output_constraints_le_input input k T))

/-- One fixed polynomial includes every declared address and every edge table. -/
noncomputable def outputPolynomial (k : Nat) (T : NoiseTables.Table s d) : Polynomial Nat :=
  let V := Polynomial.C 2 *
    (Polynomial.C (48 + CloneGap.distinctTriples.length) * Polynomial.X +
      Polynomial.C (2 ^ s) + Polynomial.C (2 ^ d) + Polynomial.C 4) ^ (1 + 9 * k)
  let E := Polynomial.C (OutputSize.edgeCoefficient k T) * Polynomial.X ^ k
  V + Polynomial.C (2 ^ s) + E + Polynomial.C 3 +
    E * (Polynomial.C 2 * V + Polynomial.C ((2 ^ s) * (2 ^ s + 1)))

theorem outputPolynomial_eval (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) :
    (outputPolynomial k T).eval inputLength = sizeBound k T inputLength := by
  simp only [outputPolynomial, sizeBound, bitsBound, vertexBound, edgeBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

theorem output_bits_polynomial_in_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T)).length ≤
        (outputPolynomial k T).eval (SourceEncoding.inputBits input).length := by
  rw [outputPolynomial_eval]
  exact output_bits_length_le input k T

theorem fixed_parameters_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits (AddressGame.tableOutput
        (UniformReduction.source input.equations input.nonempty) k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨outputPolynomial k T, fun input => output_bits_polynomial_in_input input k T⟩

def directVertexBound (k s d inputLength : Nat) : Nat :=
  2 * (inputLength + 2 ^ s + 2 ^ d + 4) ^ (1 + 9 * k)

def directEdgeCoefficient (k s d noiseCount : Nat) : Nat :=
  2 ^ ((2 * k + 1) * (s + d + 1)) * noiseCount

def directSizeBound (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) : Nat :=
  bitsBound (directVertexBound k s d inputLength)
    (directEdgeCoefficient k s d T.vectors.length * inputLength ^ k) (2 ^ s)

theorem direct_vertices_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T).vertices ≤
      directVertexBound k s d (SourceEncoding.inputBits input).length := by
  have hsum : input.variables + input.equations.length ≤
      (SourceEncoding.inputBits input).length := by
    rw [SourceEncoding.inputBits_length]
    omega
  change 2 * (CanonicalAddress.base input.variables input.equations.length s d) ^
    (1 + 9 * k) ≤ _
  rw [CanonicalAddress.base_eq]
  unfold directVertexBound
  apply Nat.mul_le_mul_left 2
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsum _) _) _

theorem direct_constraints_eq (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T).constraints.length =
      directEdgeCoefficient k s d T.vectors.length * input.equations.length ^ k := by
  rw [table_constraints_eq]
  unfold Explicit.edgeCount directEdgeCoefficient Source.ofList
  ac_rfl

theorem direct_constraints_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T).constraints.length ≤
      directEdgeCoefficient k s d T.vectors.length * (SourceEncoding.inputBits input).length ^ k := by
  rw [direct_constraints_eq]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (SourceEncoding.inputBits_length_ge_equations input) k)

theorem direct_bits_length_le (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits
      (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T)).length ≤
        directSizeBound k T (SourceEncoding.inputBits input).length :=
  (GameEncodingSize.gameBits_length_le _).trans
    (bitsBound_mono (direct_vertices_le_input input k T)
      (direct_constraints_le_input input k T))

noncomputable def directOutputPolynomial (k : Nat) (T : NoiseTables.Table s d) : Polynomial Nat :=
  let V := Polynomial.C 2 * (Polynomial.X + Polynomial.C (2 ^ s) +
    Polynomial.C (2 ^ d) + Polynomial.C 4) ^ (1 + 9 * k)
  let E := Polynomial.C (directEdgeCoefficient k s d T.vectors.length) * Polynomial.X ^ k
  V + Polynomial.C (2 ^ s) + E + Polynomial.C 3 +
    E * (Polynomial.C 2 * V + Polynomial.C ((2 ^ s) * (2 ^ s + 1)))

theorem directOutputPolynomial_eval (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) :
    (directOutputPolynomial k T).eval inputLength = directSizeBound k T inputLength := by
  simp only [directOutputPolynomial, directSizeBound, bitsBound, directVertexBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

theorem direct_bits_polynomial_in_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits
      (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T)).length ≤
        (directOutputPolynomial k T).eval (SourceEncoding.inputBits input).length := by
  rw [directOutputPolynomial_eval]
  exact direct_bits_length_le input k T

theorem fixed_parameters_direct_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits
        (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨directOutputPolynomial k T, fun input => direct_bits_polynomial_in_input input k T⟩

end UniqueGamesTheorem.Reduction.AddressOutputSize

end

end OAI
