import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FrameWireCodec
import OAI.Analysis.MatrixSigning.Encoding.FramedArraySkip

namespace OAI

namespace KS.W11.FramedArray
open KS.W01.FixedStack
open KS.W29.FixedSequential

def decoderPorts : Fin 3 ↪ Fin 4 := Fin.castLEEmb (by decide)
def decoderProgram : Program 4 := ofMachine (lift3 KS.W29.FrameDecoder.machine decoderPorts)

theorem run_decoder (payload tail ix bits : List Bool)
    (hlen : 3 * payload.length + 2 ≤ bits.length) :
    decoderProgram.toMachine.run
      (config (some decoderProgram.initial) (KS.W01.frame payload ++ tail) [] [] ix) bits =
      config none tail payload [] ix := by
  have hr (a b c : List Bool) :
      KS.W28.FixedPositiveSerializer.registers decoderPorts (fun _ => ix) a b c =
        «stacks» a b c ix := by
    funext j
    fin_cases j <;> simp [KS.W28.FixedPositiveSerializer.registers, decoderPorts, «stacks»]
  have h := KS.W11.FrameWireCodec.unframe_spec decoderPorts (fun _ => ix) payload tail
  rw [hr, hr] at h
  exact h.run_of_le bits hlen

def lookupProgram : Program 4 := compose scanProgram decoderProgram

theorem lookupProgram_states : lookupProgram.states = 6 := rfl

theorem lookupProgram_table_length : lookupProgram.table.length = 972 := by
  have generic {k : ℕ} (P Q : Program k) :
      (compose P Q).table.length = ((P.states+Q.states)*3^k)*2 := by
    unfold compose ofMachine
    change (compile (leftState P Q P.initial) P.input Q.output (dispatch P Q)).table.length = _
    rw [compile_table_length]
    simp only [Nat.mul_assoc]
  exact generic scanProgram decoderProgram

def lookupFuel («prefix» : List (List Bool)) (payload : List Bool) : ℕ :=
  scanFuel «prefix» + 3 * payload.length + 2

theorem run_lookup_prefix («prefix» : List (List Bool)) (payload tail bits : List Bool)
    (hlen : lookupFuel «prefix» payload ≤ bits.length) :
    lookupProgram.toMachine.run
      (config (some lookupProgram.initial)
        («prefix».flatMap KS.W01.frame ++ KS.W01.frame payload ++ tail)
        [] [] (List.replicate «prefix».length true)) bits =
      config none tail payload [] [] := by
  have hs : KS.W03.MachineCombinators.RunSpec scanProgram
      («stacks» («prefix».flatMap KS.W01.frame ++ KS.W01.frame payload ++ tail)
        [] [] (List.replicate «prefix».length true))
      («stacks» (KS.W01.frame payload ++ tail) [] [] []) (scanFuel «prefix») := by
    intro coins hc
    have h := scan_prefix «prefix» (KS.W01.frame payload ++ tail) [] [] coins hc
    simp only [List.append_assoc] at h ⊢
    exact h
  have hd : KS.W03.MachineCombinators.RunSpec decoderProgram
      («stacks» (KS.W01.frame payload ++ tail) [] [] []) («stacks» tail payload [] [])
      (3*payload.length+2) := by
    intro coins hc
    exact run_decoder payload tail [] coins hc.ge
  have h := hs.compose hd
  exact h.run_of_le bits (by unfold lookupFuel at hlen;omega)

theorem lookupFuel_linear («prefix» : List (List Bool)) (payload tail : List Bool) :
    lookupFuel «prefix» payload ≤
      2 * («prefix».flatMap KS.W01.frame ++ KS.W01.frame payload ++ tail).length +
        «prefix».length + 1 := by
  simp only [lookupFuel, scanFuel, List.length_append, KS.W01.length_frame]
  omega

theorem run_lookup (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (tail bits : List Bool)
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1 ≤ bits.length) :
    lookupProgram.toMachine.run
      (config (some lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true)) bits =
      config none ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) xs[i] [] [] := by
  have hx : xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have ht : (xs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hflat : xs.flatMap KS.W01.frame ++ tail =
      (xs.take i).flatMap KS.W01.frame ++ KS.W01.frame xs[i] ++
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) := by
    conv_lhs => rw [hx]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hb := lookupFuel_linear (xs.take i) xs[i]
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail)
  rw [← hflat, ht] at hb
  have h := run_lookup_prefix (xs.take i) xs[i]
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) bits (hb.trans hlen)
  simpa only [← hflat, ht] using h

theorem lookup_linear_time (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (tail : List Bool) :
    HaltsFromWithin lookupProgram
      (config (some lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true))
      (2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1) := by
  intro bits hlen
  exact congrArg (fun c => c.state) (run_lookup xs i hi tail bits hlen.ge)

end KS.W11.FramedArray

end OAI
