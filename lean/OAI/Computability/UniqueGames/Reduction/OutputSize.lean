import Mathlib.Algebra.Polynomial.Eval.Defs
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.GameEncodingSizeLemmas
import OAI.Computability.UniqueGames.Reduction.OuterCompletenessLemmas

namespace OAI

section

/-!
# Polynomial encoded length of the actual output

The encoder is the foundations team's unary, delimited forward-permutation
format. The instance is the actual list-based reduction, including canonical
body deduplication and every repeated edge occurrence. The polynomial's
coefficients depend only on the fixed gadget table and tuple dimensions.

These are output-length theorems. They do not assert a machine running-time
certificate for canonicalization, enumeration, or serialization.
-/

namespace UniqueGamesTheorem.Reduction.OutputSize

open ActualSource
open UniqueGamesTheorem.Integration
open UniqueGamesTheorem.Foundations

variable {n s d : Nat}

theorem explicitBodies_length_le (S : Source) (k s d : Nat) :
    (ActualGame.explicitBodies S k s d).length ≤
      S.occurrences ^ k * 2 ^ ((s + d) * (2 * k + 1)) := by
  let := ActualGame.orbitBodyDecidableEq S k s d
  exact (Encoding.imageVertices_length_le
    (ActualEnumeration.queries S.occurrences k s d)
    (ActualOrbit.body (ActualGame.canonical S k s d))).trans_eq
      (ActualEnumeration.length_queries S.occurrences k s d)

def vertexCoefficient (k s d : Nat) : Nat :=
  2 * CloneGap.distinctTriples.length ^ k * 2 ^ ((s + d) * (2 * k + 1))

def edgeCoefficient (k : Nat) (T : NoiseTables.Table s d) : Nat :=
  CloneGap.distinctTriples.length ^ k *
    2 ^ ((2 * k + 1) * (s + d + 1)) * T.vectors.length

private theorem collect_vertex_coefficient (m D k b : Nat) :
    2 * ((m * D) ^ k * b) = (2 * D ^ k * b) * m ^ k := by
  rw [Nat.mul_pow]
  ac_rfl

private theorem collect_edge_coefficient (m D k b p : Nat) :
    (m * D) ^ k * b * p = (D ^ k * b * p) * m ^ k := by
  rw [Nat.mul_pow]
  ac_rfl

theorem output_vertices_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (UniformReduction.output es hne k T).vertices ≤
      vertexCoefficient k s d * es.length ^ k := by
  rw [UniformReduction.output_vertex_count]
  have h := Nat.mul_le_mul_left 2
    (explicitBodies_length_le (UniformReduction.source es hne) k s d)
  calc
    _ ≤ 2 * ((UniformReduction.source es hne).occurrences ^ k *
        2 ^ ((s + d) * (2 * k + 1))) := h
    _ = 2 * ((es.length * CloneGap.distinctTriples.length) ^ k *
        2 ^ ((s + d) * (2 * k + 1))) := by rw [UniformReduction.source_occurrences]
    _ = _ := collect_vertex_coefficient _ _ _ _

theorem output_constraints_eq (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (UniformReduction.output es hne k T).constraints.length =
      edgeCoefficient k T * es.length ^ k := by
  rw [UniformReduction.output_constraint_count]
  exact collect_edge_coefficient _ _ _ _ _

def sizeBound (vertexCoeff edgeCoeff alphabet tupleLength inputLength : Nat) : Nat :=
  vertexCoeff * inputLength ^ tupleLength + alphabet +
    edgeCoeff * inputLength ^ tupleLength + 3 +
      edgeCoeff * inputLength ^ tupleLength *
        (2 * (vertexCoeff * inputLength ^ tupleLength) + alphabet * (alphabet + 1))

theorem sizeBound_mono (vertexCoeff edgeCoeff alphabet tupleLength : Nat)
    {a b : Nat} (hab : a ≤ b) :
    sizeBound vertexCoeff edgeCoeff alphabet tupleLength a ≤
      sizeBound vertexCoeff edgeCoeff alphabet tupleLength b := by
  have hp := Nat.pow_le_pow_left hab tupleLength
  have hv := Nat.mul_le_mul_left vertexCoeff hp
  have he := Nat.mul_le_mul_left edgeCoeff hp
  unfold sizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hv alphabet) he) 3)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) _))

theorem output_bits_length_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (UniformReduction.output es hne k T)).length ≤
      sizeBound (vertexCoefficient k s d) (edgeCoefficient k T) (2 ^ s) k es.length := by
  have h := GameEncodingSize.gameBits_length_le (UniformReduction.output es hne k T)
  have hv := output_vertices_le es hne k T
  rw [output_constraints_eq] at h
  apply h.trans
  unfold sizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right hv _) _) 3)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) _))

/-- An explicit polynomial for the actual serialized game. -/
noncomputable def outputPolynomial (k : Nat) (T : NoiseTables.Table s d) : Polynomial Nat :=
  let V := Polynomial.C (vertexCoefficient k s d) * Polynomial.X ^ k
  let E := Polynomial.C (edgeCoefficient k T) * Polynomial.X ^ k
  V + Polynomial.C (2 ^ s) + E + Polynomial.C 3 +
    E * (Polynomial.C 2 * V + Polynomial.C ((2 ^ s) * (2 ^ s + 1)))

theorem outputPolynomial_eval (k : Nat) (T : NoiseTables.Table s d) (m : Nat) :
    (outputPolynomial k T).eval m =
      sizeBound (vertexCoefficient k s d) (edgeCoefficient k T) (2 ^ s) k m := by
  simp [outputPolynomial, sizeBound]

theorem output_bits_polynomial_in_occurrences
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (UniformReduction.output es hne k T)).length ≤
      (outputPolynomial k T).eval es.length := by
  rw [outputPolynomial_eval]
  exact output_bits_length_le es hne k T

theorem output_bits_polynomial_in_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits
      (UniformReduction.output input.equations input.nonempty k T)).length ≤
        (outputPolynomial k T).eval (SourceEncoding.inputBits input).length := by
  rw [outputPolynomial_eval]
  exact (output_bits_length_le input.equations input.nonempty k T).trans
    (sizeBound_mono _ _ _ _ (SourceEncoding.inputBits_length_ge_equations input))

/-- Fixed reduction parameters give one polynomial for every encoded input. -/
theorem fixed_parameters_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits
        (UniformReduction.output input.equations input.nonempty k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨outputPolynomial k T, fun input => output_bits_polynomial_in_input input k T⟩

end UniqueGamesTheorem.Reduction.OutputSize

end

end OAI
