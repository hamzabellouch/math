import Mathlib
import OAI.Computability.DirectedFeedback.Machines.AddressMachineInitial

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.OutputSize

open ActualSource
open DFVSGames.Integration
open DFVSGames.Foundations

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

private theorem collect_vertex_coefficient_inline_OutputSize (m D k b : Nat) :
    2 * ((m * D) ^ k * b) = (2 * D ^ k * b) * m ^ k := by
  rw [Nat.mul_pow]
  ac_rfl

private theorem collect_edge_coefficient_inline_OutputSize (m D k b p : Nat) :
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
    _ = _ := collect_vertex_coefficient_inline_OutputSize _ _ _ _

theorem output_constraints_eq (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (UniformReduction.output es hne k T).constraints.length =
      edgeCoefficient k T * es.length ^ k := by
  rw [UniformReduction.output_constraint_count]
  exact collect_edge_coefficient_inline_OutputSize _ _ _ _ _

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

theorem fixed_parameters_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits
        (UniformReduction.output input.equations input.nonempty k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨outputPolynomial k T, fun input => output_bits_polynomial_in_input input k T⟩

end DFVSGames.Reduction.OutputSize
end

section

namespace DFVSGames.Reduction.AddressOutputSize

open ActualSource
open DFVSGames.Integration
open DFVSGames.Foundations

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

private theorem scaled_sum_le_inline_AddressOutputSize {n m N : Nat} (a b : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * a + m * b ≤ (a + b) * N := by
  calc
    _ ≤ N * a + N * b :=
      Nat.add_le_add (Nat.mul_le_mul_right a hn) (Nat.mul_le_mul_right b hm)
    _ = _ := by rw [Nat.add_mul]; ac_rfl

theorem output_constraints_eq {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (UniformReduction.source es hne) k T).constraints.length =
      edgeBound k T es.length := by
  rw [table_constraints_eq, UniformReduction.source_occurrences]
  unfold Explicit.edgeCount edgeBound OutputSize.edgeCoefficient
  rw [Nat.mul_pow]
  ring

theorem output_vertices_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T).vertices ≤
        vertexBound k s d (SourceEncoding.inputBits input).length := by
  have hn := SourceEncoding.inputBits_length_ge_variables input
  have hm := SourceEncoding.inputBits_length_ge_equations input
  have hsum := scaled_sum_le_inline_AddressOutputSize 48 CloneGap.distinctTriples.length hn hm
  change 2 * (CanonicalAddress.base
    (UniformReduction.source input.equations input.nonempty).«variables»
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
  have hsum : input.«variables» + input.equations.length ≤
      (SourceEncoding.inputBits input).length := by
    rw [SourceEncoding.inputBits_length]
    omega
  change 2 * (CanonicalAddress.base input.«variables» input.equations.length s d) ^
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

end DFVSGames.Reduction.AddressOutputSize
end

section

namespace DFVSGames.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def bits (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) : List Bool :=
  AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
    (OccurrenceTupleOrder.readCoordinates digits)

def stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressMachineProgram.Tape k T → List Bool :=
  AddressOdometerSchedule.setDigits F.equations.length (fun j => (digits j).val)
    (AddressOdometerSchedule.setAcc (AddressMachineInitial.initialized k T F) output)

theorem stateTapes_frame (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    stateTapes k T F digits output tape = AddressMachineInitial.initialized k T F tape := by
  rw [stateTapes, AddressOdometerSchedule.setDigits_other _ _ _ tape hc hr]
  exact AddressOdometerSchedule.setAcc_other _ _ tape ha

@[simp] theorem stateTapes_savedIndex (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) (j : Fin k) :
    stateTapes k T F digits output (.savedIndex j) = encodeWord (digits j.rev).val := by
  exact AddressOdometerSchedule.setDigits_savedIndex _ _ _ j

@[simp] theorem stateTapes_private (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : MachineTemplateAddress.Tape (4*k) (1+9*k)) :
    stateTapes k T F digits output (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  rw [stateTapes_frame]
  · exact AddressMachineInitial.initialized_privateAddress k T F tape
  all_goals simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem stateTapes_header (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) (hc : c ≠ .reversed) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      AddressMachineInitial.initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) := by
  apply stateTapes_frame
  · exact AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c
  · exact AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c
  · intro h
    exact hc ((AddressMachineSpace.headerTape_eq_iff k s d T.vectors.length c .reversed).mp h)

theorem stateTapes_ready (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressTupleBody.Ready F (OccurrenceTupleOrder.readCoordinates digits)
      (stateTapes k T F digits output) := by
  constructor
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_source k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j
    exact stateTapes_savedIndex k T F digits output j
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_index k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_work k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_scratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_copyScratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j slot
    rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_field k T F j slot
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

theorem stateTapes_clean (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) := by
  constructor
  · constructor
    · exact stateTapes_private k T F digits output .reversed
    · exact stateTapes_private k T F digits output .forward
    · exact stateTapes_private k T F digits output .copyScratch
    · exact stateTapes_private k T F digits output .accA
    · exact stateTapes_private k T F digits output .accB
    · exact stateTapes_private k T F digits output .counter
    · exact stateTapes_private k T F digits output .hornerScratch
    · intro j; exact stateTapes_private k T F digits output (.digit j)
  · exact stateTapes_private k T F digits output .output

theorem stateTapes_base (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_base]
  congr 1
  simp [MachineAddressHeaders.radix, MachineAddressHeaders.baseConstant,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem stateTapes_capacity (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (AddressGame.bodyCapacity (AddressTupleBody.source F) k s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_capacity]
  congr 1
  change MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
    CanonicalAddress.capacity F.«variables» F.equations.length k s d
  simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
    MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem appended_stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output payload : List Bool) :
    MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) payload =
      stateTapes k T F digits (payload.reverse ++ output) := by
  change AddressOdometerSchedule.setAcc (stateTapes k T F digits output)
    (payload.reverse ++ stateTapes k T F digits output
      (AddressOdometerSchedule.accumulator k s d T.vectors.length)) = _
  simp only [stateTapes, AddressOdometerSchedule.setDigits_accumulator, AddressOdometerSchedule.setAcc_apply]
  rw [AddressOdometerSchedule.setDigits_setAcc, AddressOdometerSchedule.setAcc_setAcc,
    ← AddressOdometerSchedule.setDigits_setAcc]

theorem bodyTrace (F : SourceEncoding.Input) :
    AddressOdometerSchedule.BodyTrace (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F)
      (bits k T F) ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  intro digits output
  let base := stateTapes k T F digits output
  have ready := stateTapes_ready k T F digits output
  have clean := stateTapes_clean k T F digits output
  have actual := AddressTuplePolynomial.run_actual T (AddressMachineProgram.bodyLabels k T) (some (AddressMachineProgram.next k T 0))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atBody k T) F
    (OccurrenceTupleOrder.readCoordinates digits) base ready clean (fun _ => false)
    (stateTapes_base k T F digits output) (stateTapes_capacity k T F digits output)
  refine ⟨actual.steps, actual.steps_le_m, ?_⟩
  have hemit : MachineAddressEdge.appended (AddressTupleBody.Slots k s d T.vectors.length)
      base (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
        (OccurrenceTupleOrder.readCoordinates digits)) =
      stateTapes k T F digits ((bits k T F digits).reverse ++ output) :=
    appended_stateTapes k T F digits output _
  exact actual.evals_in_steps.trans (congrArg
    (fun tapes => some (AddressOdometerSchedule.configuration
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 tapes)) hemit)

theorem setDigits_initialized_zero (F : SourceEncoding.Input) :
    AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
      (AddressMachineInitial.initialized k T F) = AddressMachineInitial.initialized k T F := by
  funext tape
  cases tape with
  | savedIndex j =>
    rw [AddressOdometerSchedule.setDigits_savedIndex, AddressMachineInitial.initialized_savedIndex]
  | extra e =>
    rcases e with e | e
    · rfl
    · rcases e with e | e
      · rfl
      · rcases e with j | e
        · change AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
            (AddressMachineInitial.initialized k T F) (AddressOdometerSchedule.remaining k s d T.vectors.length j) = _
          simp only [AddressOdometerSchedule.setDigits_remaining, Fin.isLt, dite_eq_left, Nat.sub_zero]
          exact (AddressMachineInitial.initialized_remaining k T F j).symm
        · rfl
  | _ => rfl

def finalTapes (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  (AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
    (AddressMachineInitial.initialized k T F) (bits k T F)).stk

def traversal (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      (((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length + 2*k) *
        F.equations.length^k) := by
  have actual := AddressOdometerSchedule.traversalInTime (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
    (AddressMachineProgram.next k T) (AddressMachineProgram.resetAt k T) (AddressMachineSpace.initialState k).1
    (List.length_pos_iff.mpr F.nonempty)
    ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length)
    (AddressMachineInitial.initialized k T F) (bits k T F)
    (by
      intro i hi
      simp only [AddressMachineProgram.next_lt k T i hi, AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atCheck k T ⟨i,hi⟩)
    (by
      intro i hi
      simp only [AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atReset k T ⟨i,hi⟩)
    (bodyTrace k T F)
  have run := Classical.choice actual
  have hstart : AddressOdometerSchedule.initialConfiguration (m := F.equations.length) k
      (AddressMachineProgram.bodyStart k T) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F) =
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩ := by
    simp only [AddressOdometerSchedule.initialConfiguration, AddressOdometerSchedule.configuration,
      setDigits_initialized_zero, AddressMachineSpace.initialState]
  have hfinish : AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
      (AddressMachineInitial.initialized k T F) (bits k T F) =
      ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩ := by
    simp only [AddressOdometerSchedule.finalConfiguration, AddressOdometerSchedule.configuration, finalTapes,
      AddressMachineProgram.next_ge k T k (Nat.le_refl _), AddressMachineSpace.initialState]
  rw [hstart, hfinish] at run
  exact run

theorem allBits_eq (F : SourceEncoding.Input) :
    AddressOdometerSchedule.allBits (bits k T F) =
      (FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T) := by
  exact (OccurrenceTupleOrder.functions_flatMap F.equations.length k _).symm

@[simp] theorem final_reversed (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      ((FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T)).reverse ++
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
  change (AddressOdometerSchedule.finalConfiguration _ _ _ _).stk (AddressOdometerSchedule.accumulator _ _ _ _) = _
  rw [AddressOdometerSchedule.final_accumulator]
  change (AddressOdometerSchedule.allBits (bits k T F)).reverse ++ _ = _
  rw [allBits_eq]
  congr 1
  exact AddressMachineInitial.initialized_reversed k T F

theorem headerBits_eq (F : SourceEncoding.Input) :
    MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
      F.«variables» F.equations.length =
      encodeWords [(AddressGame.tableOutput (AddressTupleBody.source F) k T).vertices, 2^s,
        (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length] := by
  have hcap : MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
      AddressGame.bodyCapacity (AddressTupleBody.source F) k s d := by
    change MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
      CanonicalAddress.capacity F.«variables» F.equations.length k s d
    simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
      MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
      CanonicalAddress.base_eq, Nat.add_assoc]
  have hedge : MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length := by
    rw [AddressOutputSize.table_constraints_eq]
    change MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      Explicit.edgeCount F.equations.length k (s+d) T.vectors.length
    unfold MachineAddressHeaders.edgeCount MachineAddressHeaders.edgeFactor Explicit.edgeCount
    ring
  rw [MachineAddressHeaders.Arithmetic.headerBits, hcap, hedge]
  rfl

theorem final_accumulator (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.accumulator k T) =
      (gameBits (AddressGame.tableOutput (AddressTupleBody.source F) k T)).reverse := by
  rw [AddressOutcomeSpecs.gameBits_factor, ← headerBits_eq k T F, List.reverse_append]
  exact final_reversed k T F

theorem final_other (F : SourceEncoding.Input) (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    finalTapes k T F tape = AddressMachineInitial.initialized k T F tape :=
  AddressOdometerSchedule.final_other _ _ _ _ tape hc hr ha

@[simp] theorem final_outputEmpty (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.output k T) = [] := by
  rw [final_other]
  · exact AddressMachineInitial.initialized_finalOutput k T F
  · intro j
    exact Ne.symm (AddressMachineSpace.current_ne_finalOutput k s d T.vectors.length j)
  · intro j
    exact Ne.symm (AddressMachineSpace.remaining_ne_finalOutput k s d T.vectors.length j)
  · exact Ne.symm (AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed)

@[simp] theorem final_current (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  AddressOdometerSchedule.final_current _ _ _ _ j

@[simp] theorem final_remaining (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length-1) :=
  AddressOdometerSchedule.final_remaining _ _ _ _ j

def timePolynomial : Polynomial Nat :=
  (AddressTupleBudget.timePolynomial k T + Polynomial.C (2*k)) * Polynomial.X^k

@[simp] theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N = ((AddressTupleBudget.timePolynomial k T).eval N + 2*k)*N^k := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have run := traversal k T F
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  rw [timePolynomial_eval]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (SourceEncoding.inputBits_length_ge_equations F) k)

end
end DFVSGames.Reduction.AddressMachineLoop
end

section

namespace DFVSGames.Reduction.AddressMachineFinish

open Turing Foundations.Complexity Foundations.Hastad

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def timePolynomial (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (AddressMachineProgram.machine k T)
    (AddressMachineProgram.clearKeys k T).length (prefixTime + 1)

def completePrefix (input : List Bool) (prefixTime : Polynomial Nat)
    (base : AddressMachineProgram.Tape k T → List Bool)
    (execution : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨some (AddressMachineProgram.finishStart k T),
        AddressMachineSpace.initialState k, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base (AddressMachineProgram.output k T) = []) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) input
      (some (base (AddressMachineProgram.accumulator k T)).reverse)
      ((timePolynomial k T prefixTime).eval input.length) := by
  let bridge := AddressMachineProgram.finishStartInTime k T
    (AddressMachineSpace.initialState k) base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨SourceRuntimeFinish.entry (AddressMachineProgram.clearKeys k T)
          (AddressMachineProgram.finishLabels k T), AddressMachineSpace.initialState k, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_ne_output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T)
    (AddressMachineSpace.initialState k).1 (AddressMachineProgram.finishLabels k T) none
    (AddressMachineProgram.program k T) (AddressMachineProgram.atFinish k T)
    base outputEmpty (AddressMachineSpace.initialState k).1 none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (AddressMachineProgram.machine k T)
    input (prefixTime + 1) prefixRun
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T) base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
    (initList (AddressMachineProgram.machine k T) input)
    (some (haltList (AddressMachineProgram.machine k T)
      (base (AddressMachineProgram.accumulator k T)).reverse)) _
  rw [AddressMachineProgram.haltList_eq]
  exact run

end
end DFVSGames.Reduction.AddressMachineFinish
end

section

namespace DFVSGames.Reduction.MachineAddressGame

open Turing Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def output (input : SourceEncoding.Input) : Foundations.Target.Instance (2 ^ s) :=
  AddressGame.tableOutput
    (ActualSource.Source.ofList input.equations input.nonempty) k T

def prefixPolynomial : Polynomial Nat :=
  AddressMachineInitial.timePolynomial k T + AddressMachineLoop.timePolynomial k T

def timePolynomial : Polynomial Nat :=
  AddressMachineFinish.timePolynomial k T (prefixPolynomial k T)

def prefixInTime (input : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input))
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k,
        AddressMachineLoop.finalTapes k T input⟩)
      ((prefixPolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let initial := AddressMachineInitial.inPolynomialTime k T input
  let loop := AddressMachineLoop.inPolynomialTime k T input
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm] using run.steps_le_m

def fullRunInTime (input : SourceEncoding.Input) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input)
      (some (gameBits (output k T input)))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let run := AddressMachineFinish.completePrefix k T (SourceEncoding.inputBits input)
    (prefixPolynomial k T) (AddressMachineLoop.finalTapes k T input)
    (prefixInTime k T input) (AddressMachineLoop.final_outputEmpty k T input)
  simpa only [AddressMachineLoop.final_accumulator, List.reverse_reverse, output,
    Integration.AddressTupleBody.source, timePolynomial] using run

def computableInPolyTime :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) where
  tm := AddressMachineProgram.machine k T
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial k T
  outputsFun input := by
    change TM2OutputsInTime (AddressMachineProgram.machine k T)
      ((SourceEncoding.inputBits input).map id)
      (some ((gameBits (output k T input)).map id))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length)
    dsimp only [AddressMachineProgram.machine]
    rw [List.map_id, List.map_id]
    exact fullRunInTime k T input

theorem workAlphabetFinite (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end DFVSGames.Reduction.MachineAddressGame
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
