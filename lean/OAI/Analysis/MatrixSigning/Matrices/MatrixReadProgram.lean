import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.MatrixAddressArithmetic
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAddressLookup

namespace OAI

section

namespace KS.W08.MatrixRead

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W03.MultiplicationBody KS.W03.MachineCombinators

def workspace (source col row dim address : List Bool) : Fin 8 → List Bool :=
  ![col, row, dim, address, [], [], [], source]

def addressPorts : Fin 7 ↪ Fin 8 := Fin.castLEEmb (by decide)
def accessPorts : Fin 5 ↪ Fin 8 := ⟨![7, 3, 0, 1, 2], by decide⟩
def addressProgram : Program 8 := KS.W29.FixedSequential.liftPorts MatrixAddress.program addressPorts
def accessProgram : Program 8 := KS.W29.FixedSequential.liftPorts binaryMatrixLookupProgram accessPorts

def program : Program 8 := compose addressProgram accessProgram

theorem config_ext {k q : ℕ} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

theorem run_address {n : ℕ} (source : List Bool) (i j : Fin n) (bits : List Bool)
    (hlen : 512 * (n + 1) ^ 2 ≤ bits.length) :
    addressProgram.toMachine.run
      ⟨some addressProgram.initial, workspace source (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) []⟩ bits =
      ⟨none, workspace source [] [] [] (denseMatrixBinaryCursor i j)⟩ := by
  have hs : RunSpec MatrixAddress.program
      (registers (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n) [] [] [] [])
      (registers [] [] [] (denseMatrixBinaryCursor i j) [] [] []) (512*(n+1)^2) := by
    intro coins hcoins
    exact MatrixAddress.run_matrix_address i j coins hcoins.ge
  have hl : RunSpec addressProgram
      (workspace source (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n) [])
      (workspace source [] [] [] (denseMatrixBinaryCursor i j)) (512*(n+1)^2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ addressPorts _ _ _ _ _ hs
    · intro r; fin_cases r <;> rfl
    · intro r; fin_cases r <;> rfl
    · intro r hr
      have h0 : r≠0 := hr (0 : Fin 7)
      have h1 : r≠1 := hr (1 : Fin 7)
      have h2 : r≠2 := hr (2 : Fin 7)
      have h3 : r≠3 := hr (3 : Fin 7)
      fin_cases r <;> simp_all [workspace]
  exact hl.run_of_le bits hlen

theorem run_access {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool)
    (hlen : n * n * (40 * b + 84) + 6 ≤ bits.length) :
    accessProgram.toMachine.run
      ⟨some accessProgram.initial, workspace (denseMatrixTape M) [] [] [] (denseMatrixBinaryCursor i j)⟩ bits =
      ⟨none, workspace (denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] []⟩ := by
  have hs : RunSpec binaryMatrixLookupProgram
      (KS.W04.ReusableArrayLookup.arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [])
      (KS.W04.ReusableArrayLookup.arrayStacks (denseMatrixTape M) []
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [])
      (n*n*(40*b+84)+6) := by
    intro coins hcoins
    simpa only [AccessCounted.readMatrix_value] using
      run_binaryMatrix_lookup M b hnum hden i j coins hcoins.ge
  have hl : RunSpec accessProgram
      (workspace (denseMatrixTape M) [] [] [] (denseMatrixBinaryCursor i j))
      (workspace (denseMatrixTape M) (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] [])
      (n*n*(40*b+84)+6) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ accessPorts _ _ _ _ _ hs
    · intro r; fin_cases r <;> rfl
    · intro r; fin_cases r <;> rfl
    · intro r hr
      have h0 : r≠0 := hr (2 : Fin 5)
      have h3 : r≠3 := hr (1 : Fin 5)
      fin_cases r <;> simp_all [workspace]
  exact hl.run_of_le bits hlen

theorem run_matrix_read {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool)
    (hlen : 1024 * (n + 1) ^ 2 * (b + 1) ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, workspace (denseMatrixTape M) (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) []⟩ bits =
      ⟨none, workspace (denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] []⟩ := by
  apply KS.W04.ReusableArrayLookup.run_compose_bounded addressProgram accessProgram
    (workspace (denseMatrixTape M) (Computability.encodeNat j.val)
      (Computability.encodeNat i.val) (Computability.encodeNat n) [])
    (workspace (denseMatrixTape M) [] [] [] (denseMatrixBinaryCursor i j))
    (workspace (denseMatrixTape M) (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] [])
    (512 * (n + 1) ^ 2) (n * n * (40 * b + 84) + 6)
  · exact run_address (denseMatrixTape M) i j
  · exact run_access M b hnum hden i j
  · have hb : 512 * (n + 1) ^ 2 + (n * n * (40 * b + 84) + 6) ≤
        1024 * (n + 1) ^ 2 * (b + 1) := by ring_nf; omega
    exact hb.trans hlen

theorem matrix_read_time {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    HaltsFromWithin program
      ⟨some program.initial, workspace (denseMatrixTape M) (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) []⟩
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
  intro bits hlen
  exact congrArg Config.state (run_matrix_read M b hnum hden i j bits hlen.ge)

def liftedProgram {k : ℕ} (ports : Fin 8 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts program ports

theorem run_matrix_read_ports {k n : ℕ} (ports : Fin 8 ↪ Fin k)
    (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool) (c : Config k program.states)
    (hc : projectPorts ports c =
      ⟨some program.initial, workspace (denseMatrixTape M) (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) []⟩)
    (hlen : 1024 * (n + 1) ^ 2 * (b + 1) ≤ bits.length) :
    let result := (liftedProgram ports).toMachine.run c bits
    projectPorts ports result =
      ⟨none, workspace (denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] []⟩ ∧
    ∀ r, (∀ s, r ≠ ports s) → result.«stacks» r = c.«stacks» r := by
  have h := KS.W01.FixedStack.liftPorts_project_run program.toMachine ports c bits
  erw [hc, run_matrix_read M b hnum hden i j bits hlen] at h
  refine ⟨h, ?_⟩
  intro r hr
  exact KS.W01.FixedStack.liftPorts_run_preserves_other program.toMachine ports c bits r hr

end KS.W08.MatrixRead

end

end OAI
