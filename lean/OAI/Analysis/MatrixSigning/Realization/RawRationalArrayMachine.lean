import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteControl
import OAI.Analysis.MatrixSigning.Machines.LiteralProgram
import OAI.Analysis.MatrixSigning.Potential.Normalizer
import OAI.Analysis.MatrixSigning.Realization.RawRationalBounds

namespace OAI

namespace CurrentKS.RawRationalArrayMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W01

def extend (s : Fin 14 → List Bool) (acc count : List Bool) : Fin 16 → List Bool :=
  fun j => if hj : j.val < 14 then s ⟨j.val,hj⟩ else if j.val = 14 then acc else count

def state (source value acc count : List Bool) : Fin 16 → List Bool :=
  extend (RawRationalMachine.state source value [] []) acc count

def ports : Fin 14 ↪ Fin 16 := ⟨Fin.castAdd 2, Fin.castAdd_injective 14 2⟩
def normalizer : Program 16 := liftPorts RawRationalMachine.program ports
def framePorts : Fin 3 ↪ Fin 16 := ⟨![0,10,1],by decide⟩
def framing : Program 16 := KS.W11.FrameWireCodec.frameProgram framePorts
def appendFrame : Program 16 := KS.W04.BinaryStackMoves.moveProgram 10 14
def popCount : Program 16 := KS.W23.LiteralProgram.pop 15
def body : Program 16 := compose normalizer (compose framing (compose appendFrame popCount))
def scan : Program 16 := FiniteControl.whileNonempty 15 body
def finish : Program 16 := KS.W04.BinaryStackMoves.moveProgram 14 10
def program : Program 16 := compose scan finish

def rawTape (entries : List RationalEntry) : List Bool := entries.flatMap RationalEntry.encode
def canonicalTape (entries : List RationalEntry) : List Bool :=
  entries.flatMap (fun a => KS.W01.frame (encodeRat a.value))
def unary (n : ℕ) : List Bool := List.replicate n true

@[simp] lemma extend_port (s : Fin 14 → List Bool) (acc count : List Bool) (i : Fin 14) :
    extend s acc count (ports i) = s i := by simp [extend,ports]

lemma extend_other (s t : Fin 14 → List Bool) (acc count : List Bool)
    (j : Fin 16) (hj : ∀ i, j ≠ ports i) :
    extend t acc count j = extend s acc count j := by
  by_cases h : j.val < 14
  · exact (hj ⟨j.val,h⟩ (Fin.ext rfl)).elim
  · simp [extend,h]

lemma normalizer_spec (a : RationalEntry) (tail acc count : List Bool) :
    RunSpec normalizer (state (a.encode++tail) [] acc count)
      (state tail (encodeRat a.value) acc count) (400*(a.encode.length+1)^3) := by
  exact KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _
    (RawRationalMachine.polynomial_spec a tail)
    (extend_port _ _ _) (extend_port _ _ _) (extend_other _ _ _ _)

lemma framing_spec (source value acc count : List Bool) :
    RunSpec framing (state source value acc count)
      (state source (KS.W01.frame value) acc count) (4*value.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec framePorts (state source [] acc count) value
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [state,extend,RawRationalMachine.state,framePorts,
      KS.W28.FixedPositiveSerializer.registers]

lemma appendFrame_spec (source value acc count : List Bool) :
    RunSpec appendFrame (state source value acc count)
      (state source [] (value.reverse++acc) count) (value.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (10 : Fin 16) 14 (by decide)
    (state source value acc count)
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [state,extend,RawRationalMachine.state,KS.W15.RationalMultiply.moveAfter]

lemma popCount_spec (source acc : List Bool) (n : ℕ) :
    RunSpec popCount (state source [] acc (unary (n+1)))
      (state source [] acc (unary n)) 1 := by
  have h := KS.W23.LiteralProgram.pop_spec (15 : Fin 16)
    (state source [] acc (unary (n+1)))
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [state,extend,RawRationalMachine.state,unary,Function.update]

def bodyTicks (a : RationalEntry) : ℕ :=
  400*(a.encode.length+1)^3+(4*(encodeRat a.value).length+3)+
    ((KS.W01.frame (encodeRat a.value)).length+1)+1

lemma body_spec (a : RationalEntry) (tail acc : List Bool) (n : ℕ) :
    RunSpec body (state (a.encode++tail) [] acc (unary (n+1)))
      (state tail [] ((KS.W01.frame (encodeRat a.value)).reverse++acc) (unary n)) (bodyTicks a) := by
  have h := (normalizer_spec a tail acc (unary (n+1))).compose
    ((framing_spec tail (encodeRat a.value) acc (unary (n+1))).compose
      ((appendFrame_spec tail (KS.W01.frame (encodeRat a.value)) acc (unary (n+1))).compose
        (popCount_spec tail ((KS.W01.frame (encodeRat a.value)).reverse++acc) n)))
  have ht : 400*(a.encode.length+1)^3+((4*(encodeRat a.value).length+3)+
      (((KS.W01.frame (encodeRat a.value)).length+1)+1)) = bodyTicks a := by
    simp only [bodyTicks]; omega
  rw [ht] at h
  exact h

lemma bodyTicks_le (a : RationalEntry) (L : ℕ) (ha : a.encode.length ≤ L) :
    bodyTicks a ≤ 450*(L+1)^3 := by
  have hv := RawRationalMachine.value_wire_length a
  have hp : (a.encode.length+1)^3 ≤ (L+1)^3 := Nat.pow_le_pow_left (by omega) _
  have hl : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  simp only [bodyTicks,length_frame]
  nlinarith

lemma scan_trace (entries : List RationalEntry) (tail acc : List Bool) (L : ℕ)
    (hL : ∀ a ∈ entries, a.encode.length ≤ L) :
    FiniteControl.Trace (15 : Fin 16) body
      (state (rawTape entries++tail) [] acc (unary entries.length))
      (state tail [] ((canonicalTape entries).reverse++acc) [])
      (entries.length*(450*(L+1)^3+1)+1) := by
  induction entries generalizing acc with
  | nil =>
    simpa [rawTape,canonicalTape,unary] using
      (FiniteControl.Trace.stop (body := body) (port := (15 : Fin 16))
        (state tail [] acc []) (by simp [state,extend]))
  | cons a entries ih =>
    have hb := (body_spec a (rawTape entries++tail) acc entries.length).mono
      (bodyTicks_le a L (hL a (by simp)))
    have ht := ih ((KS.W01.frame (encodeRat a.value)).reverse++acc)
      (fun b hb => hL b (by simp [hb]))
    have hs : state (a.encode++(rawTape entries++tail)) [] acc
        (unary (entries.length+1)) (15 : Fin 16) ≠ [] := by
      simp [state,extend,unary]
    have h := FiniteControl.Trace.step hs hb ht
    have hc : 450*(L+1)^3+(entries.length*(450*(L+1)^3+1)+1)+1 =
        (entries.length+1)*(450*(L+1)^3+1)+1 := by ring
    rw [hc] at h
    simpa [rawTape,canonicalTape,List.reverse_append,List.append_assoc] using h

lemma finish_spec (tail word : List Bool) :
    RunSpec finish (state tail [] word.reverse []) (state tail word [] []) (word.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (14 : Fin 16) 10 (by decide)
    (state tail [] word.reverse [])
  convert h using 1 <;> (try rfl) <;> try simp [state,extend]
  funext j
  fin_cases j <;> simp [extend,RawRationalMachine.state,KS.W15.RationalMultiply.moveAfter]

theorem program_spec (entries : List RationalEntry) (tail : List Bool) (L : ℕ)
    (hL : ∀ a ∈ entries, a.encode.length ≤ L) :
    RunSpec program (state (rawTape entries++tail) [] [] (unary entries.length))
      (state tail (canonicalTape entries) [] [])
      ((entries.length*(450*(L+1)^3+1)+1)+(canonicalTape entries).length+1) := by
  have h1 := FiniteControl.trace_spec (scan_trace entries tail [] L hL)
  simp only [List.append_nil] at h1
  have h := h1.compose (finish_spec tail (canonicalTape entries))
  simp only [Nat.add_assoc] at h ⊢
  exact h

lemma member_length_le (entries : List RationalEntry) (a : RationalEntry) (ha : a ∈ entries) :
    a.encode.length ≤ (rawTape entries).length := by
  induction entries with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    simp only [rawTape,List.flatMap_cons,List.length_append]
    rcases ha with rfl | ha
    · omega
    · exact (ih ha).trans (Nat.le_add_left _ _)

lemma count_le_raw (entries : List RationalEntry) : entries.length ≤ (rawTape entries).length := by
  induction entries with
  | nil => simp [rawTape]
  | cons a as ih =>
    have he := RawRationalMachine.entry_length a
    simp only [rawTape,List.flatMap_cons,List.length_append,List.length_cons] at *
    omega

lemma canonical_length_le (entries : List RationalEntry) :
    (canonicalTape entries).length ≤ 4*(rawTape entries).length := by
  induction entries with
  | nil => simp [rawTape,canonicalTape]
  | cons a as ih =>
    have he := RawRationalMachine.entry_length a
    have hv := RawRationalMachine.value_wire_length a
    simp only [rawTape,canonicalTape,List.flatMap_cons,List.length_append,length_frame] at *
    omega

theorem polynomial_spec (entries : List RationalEntry) (tail : List Bool) :
    RunSpec program (state (rawTape entries++tail) [] [] (unary entries.length))
      (state tail (canonicalTape entries) [] []) (500*((rawTape entries).length+1)^4) := by
  apply (program_spec entries tail (rawTape entries).length
    (fun a ha => member_length_le entries a ha)).mono
  have hn := count_le_raw entries
  have hv := canonical_length_le entries
  have hm := Nat.mul_le_mul_right (450*((rawTape entries).length+1)^3+1) hn
  nlinarith [Nat.zero_le ((rawTape entries).length^3),
    Nat.zero_le ((rawTape entries).length^4)]

end CurrentKS.RawRationalArrayMachine

end OAI
