import Mathlib
import OAI.Analysis.MatrixSigning.Model
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Encoding.FrameWireCodec

namespace OAI

namespace CurrentKS.DenseInputMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

lemma frame_eq (bs : List Bool) : CurrentKS.frame bs = KS.W01.frame bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [CurrentKS.frame, KS.W01.frame, ih]

lemma encodeNat_eq (n : ℕ) : CurrentKS.encodeNat n = KS.W01.encodeNat n :=
  frame_eq _

lemma encodeInt_eq (z : ℤ) : CurrentKS.encodeInt z = KS.W01.encodeInt z := by
  cases z <;> simp only [CurrentKS.encodeInt, KS.W01.encodeInt, encodeNat_eq]

def layout (source dim count scratch output : List Bool) : Fin 5 → List Bool :=
  ![source, dim, count, scratch, output]

def dimPorts : Fin 3 ↪ Fin 5 := ⟨![0, 1, 3], by decide⟩
def countPorts : Fin 3 ↪ Fin 5 := ⟨![0, 2, 3], by decide⟩
def readDimension : Program 5 := KS.W11.FrameWireCodec.unframeProgram dimPorts
def readCount : Program 5 := KS.W11.FrameWireCodec.unframeProgram countPorts
def readHeader : Program 5 := compose readDimension readCount

def denseTape (x : Input) : List Bool := (List.ofFn x.encodeMatrix).flatten

def headerTicks (d N : ℕ) : ℕ :=
  3 * (Computability.encodeNat d).length +
    3 * (Computability.encodeNat N).length + 4

lemma readDimension_spec (d : ℕ) (tail output : List Bool) :
    RunSpec readDimension (layout (CurrentKS.encodeNat d ++ tail) [] [] [] output)
      (layout tail (Computability.encodeNat d) [] [] output)
      (3 * (Computability.encodeNat d).length + 2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec dimPorts
    (layout [] [] [] [] output) (Computability.encodeNat d) tail
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [layout, dimPorts, KS.W28.FixedPositiveSerializer.registers,
      CurrentKS.encodeNat, frame_eq]

lemma readCount_spec (N : ℕ) (tail dim output : List Bool) :
    RunSpec readCount (layout (CurrentKS.encodeNat N ++ tail) dim [] [] output)
      (layout tail dim (Computability.encodeNat N) [] output)
      (3 * (Computability.encodeNat N).length + 2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec countPorts
    (layout [] dim [] [] output) (Computability.encodeNat N) tail
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [layout, countPorts, KS.W28.FixedPositiveSerializer.registers,
      CurrentKS.encodeNat, frame_eq]

theorem readHeader_spec (x : Input) (output : List Bool) :
    RunSpec readHeader (layout x.encode [] [] [] output)
      (layout (denseTape x) (Computability.encodeNat x.d)
        (Computability.encodeNat x.N) [] output) (headerTicks x.d x.N) := by
  have h := (readDimension_spec x.d (CurrentKS.encodeNat x.N ++ denseTape x) output).compose
    (readCount_spec x.N (denseTape x) (Computability.encodeNat x.d) output)
  convert h using 1 <;> (try rfl)
  · simp only [Input.encode, denseTape, List.append_assoc]
  · unfold headerTicks
    omega

lemma length_frame (bs : List Bool) : (CurrentKS.frame bs).length = 2 * bs.length + 1 := by
  rw [frame_eq]
  exact KS.W01.length_frame bs

theorem headerTicks_le (x : Input) : headerTicks x.d x.N ≤ 2 * x.length := by
  simp only [headerTicks, Input.length, Input.encode, List.length_append,
    CurrentKS.encodeNat, length_frame]
  omega

lemma denseTape_length_le (x : Input) : (denseTape x).length ≤ x.length := by
  simp only [Input.length, Input.encode, denseTape, List.length_append]
  omega

lemma matrixTape_nonempty (x : Input) (i : Fin x.N) : x.encodeMatrix i ≠ [] := by
  simp [Input.encodeMatrix]

lemma denseTape_eq_nil_iff (x : Input) : denseTape x = [] ↔ x.N = 0 := by
  unfold denseTape
  rw [List.flatten_eq_nil_iff]
  constructor
  · intro h
    by_contra hn
    have h0 : x.encodeMatrix ⟨0, Nat.pos_of_ne_zero hn⟩ = [] :=
      h _ (List.mem_ofFn.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩, rfl⟩)
    exact matrixTape_nonempty x _ h0
  · intro h l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    have hi := i.isLt
    omega

lemma denseTape_dim_zero (x : Input) (hd : x.d = 0) :
    denseTape x = List.replicate x.N true := by
  have ha : ∀ i : Fin x.N, x.encodeMatrix i = [true] := by
    intro i
    have he : List.ofFn (fun j : Fin x.d =>
        (List.ofFn fun k : Fin x.d => x.entries i j k).flatMap encodeComplex) = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hd
    simp [Input.encodeMatrix, he]
  unfold denseTape
  rw [show x.encodeMatrix = (fun _ => [true]) from funext ha]
  simp

def trivialTail : Program 5 := KS.W04.BinaryStackMoves.moveProgram 0 4

def trivialProgram : Program 5 := compose readHeader trivialTail

lemma trivialTail_spec (source dim count : List Bool) :
    RunSpec trivialTail (layout source dim count [] [])
      (layout [] dim count [] source.reverse) (source.length + 1) := by
  have h := KS.W15.RationalMultiply.move_spec (0 : Fin 5) 4 (by decide)
    (layout source dim count [] [])
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [layout, KS.W15.RationalMultiply.moveAfter]

theorem trivialProgram_spec (x : Input) (ht : x.N = 0 ∨ x.d = 0) :
    RunSpec trivialProgram (layout x.encode [] [] [] [])
      (layout [] (Computability.encodeNat x.d) (Computability.encodeNat x.N)
        [] (List.replicate x.N true)) (3 * x.length + 1) := by
  have hdense : denseTape x = List.replicate x.N true := by
    rcases ht with hN | hd
    · rw [(denseTape_eq_nil_iff x).2 hN, hN]
      rfl
    · exact denseTape_dim_zero x hd
  have h := (readHeader_spec x []).compose
    (trivialTail_spec (denseTape x) (Computability.encodeNat x.d)
      (Computability.encodeNat x.N))
  rw [hdense, List.reverse_replicate] at h
  apply h.mono
  have h1 := headerTicks_le x
  have h2 := denseTape_length_le x
  rw [hdense, List.length_replicate] at h2
  simp only [List.length_replicate]
  omega

lemma trivialOutput_good (x : Input) (ht : x.N = 0 ∨ x.d = 0) :
    GoodOutput x (List.replicate x.N true) := by
  refine ⟨List.length_replicate .., ?_⟩
  have hs : signedSum x (List.replicate x.N true) = 0 := by
    rcases ht with hN | hd
    · have : IsEmpty (Fin x.N) := ⟨fun i => by have hi := i.isLt; omega⟩
      simp [signedSum]
    · ext i j
      have hi := i.isLt
      omega
  rw [hs]
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (0 : Matrix (Fin x.d) (Fin x.d) ℂ)‖ ≤ _
  simp only [map_zero, norm_zero]
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

end CurrentKS.DenseInputMachine

end OAI
