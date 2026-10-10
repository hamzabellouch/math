import OAI.Computability.DepthThree.TapeCopyAdd
import OAI.Computability.DepthThree.TapeMultiply
import OAI.Computability.DepthThree.LanguageParameters
import Mathlib.Tactic.Ring

namespace OAI

namespace DepthThreeLowerBound
namespace TapeInputGuard

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

def requiredLength (d r t : ℕ) : ℕ := d + (d + r - 1) + r + t * r

theorem requiredLength_parameters (d : ℕ) :
    requiredLength d (hashDimension d) (independenceOrder d) = blockLen d := rfl

def outputStore (σ : TapeStore) (d r t : ℕ) : TapeStore :=
  Function.update σ 8 (List.replicate (requiredLength d r t) true)

@[simp] theorem outputStore_length (σ : TapeStore) (d r t : ℕ) :
    outputStore σ d r t 8 = List.replicate (requiredLength d r t) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (d r t : ℕ) (q : TapeRegister)
    (hq : q ≠ 8) : outputStore σ d r t q = σ q := by
  simp [outputStore, Function.update, hq]

abbrev ProductState := TapeCopy.State ⊕ TapeMultiply.State

def productProgram : TapeMultiProgram ProductState :=
  joinCode (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 8)
    (fun _ => TapeMultiply.start)

def productStart : ProductState := .inl .start
def productDone : ProductState := .inr TapeMultiply.done

theorem runs_product (σ : TapeStore) (t r z : ℕ)
    (h3 : σ 3 = List.replicate r true) (h4 : σ 4 = List.replicate t true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = List.replicate z true) :
    RunsIn productProgram.step (cfg productStart (storeTapes σ))
      (cfg productDone (storeTapes (Function.update σ 8 (List.replicate (z + t*r) true))))
      (t * (10*r + 14) + 2*t + 8) := by
  let τ := Function.update σ 5 (List.replicate t true)
  have hc := TapeStoreRuns.copy (src := 4) (dst := 5) (by decide) σ h5
  have hc' : RunsIn (TapeCopy.code 4 5).step (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τ)) (2*t+4) := by
    simpa only [τ, h4, List.length_replicate] using hc
  have hin : TapeMultiply.tapes 5 3 6 8 (storeTapes σ) t r 0 z = storeTapes τ := by
    funext q
    by_cases hq5 : q = 5
    · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape]
    · by_cases hq3 : q = 3
      · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h3]
      · by_cases hq6 : q = 6
        · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h6]
        · by_cases hq8 : q = 8
          · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h8]
          · simp [TapeMultiply.tapes, onPair, storeTapes, τ, hq5, hq3, hq6, hq8]
  have hout : TapeMultiply.tapes 5 3 6 8 (storeTapes σ) 0 r 0 (z+t*r) =
      storeTapes (Function.update σ 8 (List.replicate (z+t*r) true)) := by
    funext q
    by_cases hq5 : q = 5
    · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h5]
    · by_cases hq3 : q = 3
      · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h3]
      · by_cases hq6 : q = 6
        · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h6]
        · by_cases hq8 : q = 8
          · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
          · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update,
              hq5, hq3, hq6, hq8]
  have hm := TapeMultiply.runs_mul (outer := 5) (source := 3) (scratch := 6)
    (destination := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (storeTapes σ) t r z
  rw [hin, hout] at hm
  have h := join_runs (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 8)
    (fun _ => TapeMultiply.start) hc' rfl hm
  have ht : (2*t+4)+1+(t*(10*r+14)+3) = t*(10*r+14)+2*t+8 := by omega
  simpa only [productProgram, productStart, productDone, ht] using h

abbrev RingSumState := TapeCopyAdd.State ⊕ TapeCopyAdd.State
def ringSumProgram : TapeMultiProgram RingSumState :=
  joinCode (TapeCopyAdd.program 3 5 8) (TapeCopyAdd.program 3 5 8)
    (fun _ => TapeCopyAdd.start)
def ringSumStart : RingSumState := .inl TapeCopyAdd.start
def ringSumDone : RingSumState := .inr TapeCopyAdd.done

abbrev AddSumState := TapeCopyAdd.State ⊕ RingSumState
def addSumProgram : TapeMultiProgram AddSumState :=
  joinCode (TapeCopyAdd.program 2 5 8) ringSumProgram (fun _ => ringSumStart)
def addSumStart : AddSumState := .inl TapeCopyAdd.start
def addSumDone : AddSumState := .inr ringSumDone

abbrev SumState := TapeCopy.State ⊕ AddSumState
def sumProgram : TapeMultiProgram SumState :=
  joinCode (TapeCopy.code 2 8) addSumProgram (fun _ => addSumStart)
def sumStart : SumState := .inl .start
def sumDone : SumState := .inr addSumDone

theorem runs_sum (σ : TapeStore) (d r : ℕ)
    (h2 : σ 2 = List.replicate d true) (h3 : σ 3 = List.replicate r true)
    (h5 : σ 5 = []) (h8 : σ 8 = []) :
    RunsIn sumProgram.step (cfg sumStart (storeTapes σ))
      (cfg sumDone (storeTapes (Function.update σ 8 (List.replicate (d+d+r+r) true))))
      (12*d+20*r+31) := by
  let σ1 := Function.update σ 8 (List.replicate d true)
  let σ2 := Function.update σ 8 (List.replicate (d+d) true)
  let σ3 := Function.update σ 8 (List.replicate (d+d+r) true)
  have hc := TapeStoreRuns.copy (src := 2) (dst := 8) (by decide) σ h8
  have hc' : RunsIn (TapeCopy.code 2 8).step (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes σ1)) (2*d+4) := by
    simpa only [σ1, h2, List.length_replicate] using hc
  have ha := TapeCopyAdd.runs_add (src := 2) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ1 d d (by simp [σ1, h2]) (by simp [σ1]) (by simp [σ1, h5])
  have ha' : RunsIn (TapeCopyAdd.program 2 5 8).step
      (cfg TapeCopyAdd.start (storeTapes σ1)) (cfg TapeCopyAdd.done (storeTapes σ2))
      (10*d+8) := by simpa only [σ1, σ2, Function.update_idem] using ha
  have hb := TapeCopyAdd.runs_add (src := 3) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ2 r (d+d) (by simp [σ2, h3]) (by simp [σ2])
    (by simp [σ2, h5])
  have hb' : RunsIn (TapeCopyAdd.program 3 5 8).step
      (cfg TapeCopyAdd.start (storeTapes σ2)) (cfg TapeCopyAdd.done (storeTapes σ3))
      (10*r+8) := by simpa only [σ2, σ3, Function.update_idem] using hb
  have he := TapeCopyAdd.runs_add (src := 3) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ3 r (d+d+r) (by simp [σ3, h3]) (by simp [σ3])
    (by simp [σ3, h5])
  simp only [σ3, Function.update_idem] at he
  have hr := join_runs (TapeCopyAdd.program 3 5 8) (TapeCopyAdd.program 3 5 8)
    (fun _ => TapeCopyAdd.start) hb' rfl he
  have hd := join_runs (TapeCopyAdd.program 2 5 8) ringSumProgram
    (fun _ => ringSumStart) ha' rfl hr
  have h := join_runs (TapeCopy.code 2 8) addSumProgram
    (fun _ => addSumStart) hc' rfl hd
  have ht : (2*d+4)+1+((10*d+8)+1+((10*r+8)+1+(10*r+8))) =
      12*d+20*r+31 := by omega
  simpa only [sumProgram, sumStart, sumDone, addSumProgram, addSumStart, addSumDone,
    ringSumProgram, ringSumStart, ringSumDone, ht] using h

abbrev TailState := DecState ⊕ ProductState
def tailProgram : TapeMultiProgram TailState :=
  joinCode (decProgram 8) productProgram (fun _ => productStart)
def tailStart : TailState := .inl .start
def tailDone : TailState := .inr productDone

abbrev LengthState := SumState ⊕ TailState
def lengthProgram : TapeMultiProgram LengthState :=
  joinCode sumProgram tailProgram (fun _ => tailStart)
def lengthStart : LengthState := .inl sumStart
def lengthDone : LengthState := .inr tailDone

def lengthCost (d r t : ℕ) : ℕ := 12*d+20*r+16*t+10*(t*r)+45

theorem runs_length (σ : TapeStore) (d r t : ℕ)
    (h2 : σ 2 = List.replicate d true) (h3 : σ 3 = List.replicate r true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h8 : σ 8 = []) :
    RunsIn lengthProgram.step (cfg lengthStart (storeTapes σ))
      (cfg lengthDone (storeTapes (outputStore σ d r t))) (lengthCost d r t) := by
  let z := d+d+r+r
  let σS := Function.update σ 8 (List.replicate z true)
  let σD := Function.update σ 8 (List.replicate (z-1) true)
  have hs := runs_sum σ d r h2 h3 h5 h8
  have hd := decrement 8 (storeTapes σS) z (by simp [σS, storeTapes, counterTape])
  have hd' : RunsIn (decProgram 8).step (cfg DecState.start (storeTapes σS))
      (cfg (DecState.done (decide (0 < z))) (storeTapes σD)) 4 := by
    simpa only [σS, σD, ← storeTapes_update, counterTape, Function.update_idem] using hd
  have hp := runs_product σD t r (z-1) (by simp [σD, h3]) (by simp [σD, h4])
    (by simp [σD, h5]) (by simp [σD, h6]) (by simp [σD])
  have hz : z-1 = d+(d+r-1)+r := by dsimp [z]; omega
  have ho : Function.update σD 8 (List.replicate (z-1+t*r) true) =
      outputStore σ d r t := by
    simp only [σD, Function.update_idem, outputStore, requiredLength, hz]
  rw [ho] at hp
  have htail := join_runs (decProgram 8) productProgram (fun _ => productStart) hd' rfl hp
  have h := join_runs sumProgram tailProgram (fun _ => tailStart) hs rfl htail
  have ht : (12*d+20*r+31)+1+(4+1+(t*(10*r+14)+2*t+8)) =
      lengthCost d r t := by unfold lengthCost; ring
  simpa only [lengthProgram, lengthStart, lengthDone, tailProgram, tailStart, tailDone,
    σS, z, ht] using h

@[simp] theorem lengthProgram_done (h : TapeHeads) : lengthProgram lengthDone h = none := rfl

end TapeInputGuard
end DepthThreeLowerBound

end OAI
