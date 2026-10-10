import OAI.Computability.DepthThree.TapeInputBlocks

namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerTake

open TapeMultiProgram TapeRouting TapeRegister TapeInputBlockLoop

def registers : Registers where
  toFun i := match i.val with
    | 0 => productBits
    | 1 => indexA
    | 2 => loop1
    | 3 => scratchA
    | _ => accumBits
  inj' := by decide

abbrev PrepareState := TapeErase.State ⊕ TapeCopy.State
abbrev WorkState := PrepareState ⊕ TapeInputBlocks.State
abbrev State := WorkState ⊕ TapeErase.State

def prepare : TapeMultiProgram PrepareState :=
  joinCode (TapeErase.code accumBits) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start)

def work : TapeMultiProgram WorkState :=
  joinCode prepare (TapeInputBlocks.program registers) (fun _ => TapeInputBlocks.start)

def program : TapeMultiProgram State :=
  joinCode work (TapeErase.code productBits) (fun _ => TapeErase.State.start)

def start : State := .inl (.inl (.inl TapeErase.State.start))
def done : State := .inr TapeErase.State.done

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_take (σ : TapeStore) (a c : List Bool) (r : ℕ)
    (hacc : σ accumBits = a) (hprod : σ productBits = c)
    (hlenA : a.length = r) (hlenC : c.length = 2 * r)
    (hdegree : σ ringDegree = List.replicate r true)
    (hcount : σ loop1 = []) (hindex : σ indexA = []) (hscratch : σ scratchA = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update
        (Function.update σ accumBits (c.take r)) productBits [])))
      (r * (r + 27) + 8 * r + 29) := by
  let U := Function.update σ accumBits []
  let V := Function.update U loop1 (List.replicate r true)
  let W := Function.update U accumBits (c.take r)
  have he := TapeStoreRuns.erase accumBits σ
  have he' : RunsIn (TapeErase.code accumBits).step
      (cfg TapeErase.State.start (storeTapes σ)) (cfg TapeErase.State.done (storeTapes U))
      (2 * r + 5) := by
    simpa only [hacc, hlenA] using he
  have hc := TapeStoreRuns.copy (src := ringDegree) (dst := loop1) (by decide) U
    (by simp [U, hcount, accumBits, loop1])
  have hc' : RunsIn (TapeCopy.code ringDegree loop1).step
      (cfg TapeCopy.State.start (storeTapes U)) (cfg TapeCopy.State.done (storeTapes V))
      (2 * r + 4) := by
    simpa [V, U, hdegree, ringDegree, accumBits] using hc
  have hp := join_runs (TapeErase.code accumBits) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start) he' rfl hc'
  have hlen : (c.take r).length = r := by
    apply List.length_take_of_le
    omega
  have hb := TapeInputBlocks.runs_extract registers V [] (c.take r) (c.drop r) []
    (by simp [registers, source, V, U, hprod, productBits, loop1, accumBits])
    (by simp [registers, index, V, U, hindex, indexA, loop1, accumBits])
    (by simp [registers, count, V, hlen])
    (by simp [registers, scratch, V, U, hscratch, scratchA, loop1, accumBits])
    (by simp [registers, destination, V, U, loop1, accumBits])
  have hout : Function.update (Function.update V (count registers) [])
      (destination registers) (c.take r ++ []) = W := by
    funext q
    by_cases hl : q = loop1 <;> by_cases ha : q = accumBits <;>
      simp_all [V, U, W, count, destination, registers, Function.update_apply]
  have hb' : RunsIn (TapeInputBlocks.program registers).step
      (cfg TapeInputBlocks.start (storeTapes V)) (cfg TapeInputBlocks.done (storeTapes W))
      (r * (r + 27) + 12) := by
    simpa only [hout, hlen, List.length_nil, Nat.mul_zero, Nat.zero_add] using hb
  have hw := join_runs prepare (TapeInputBlocks.program registers)
    (fun _ => TapeInputBlocks.start) hp rfl hb'
  have hclear := TapeStoreRuns.erase productBits W
  have hclear' : RunsIn (TapeErase.code productBits).step
      (cfg TapeErase.State.start (storeTapes W))
      (cfg TapeErase.State.done (storeTapes (Function.update W productBits [])))
      (4 * r + 5) := by
    simpa [W, U, hprod, hlenC, productBits, accumBits, ← Nat.mul_assoc] using hclear
  have hall := join_runs work (TapeErase.code productBits)
    (fun _ => TapeErase.State.start) hw rfl hclear'
  have hfinal : Function.update W productBits [] =
      Function.update (Function.update σ accumBits (c.take r)) productBits [] := by
    simp only [W, U, Function.update_idem]
  have ht : ((2 * r + 5 + 1 + (2 * r + 4)) + 1 + (r * (r + 27) + 12)) +
      1 + (4 * r + 5) = r * (r + 27) + 8 * r + 29 := by omega
  have ht' : ((2 * r + 5 + 1 + (2 * r + 4)) + 1 + (r * (r + 27) + 12)) +
      1 + (4 * r + 5) ≤ r * (r + 27) + 8 * r + 29 := ht.le
  have h := hall.mono ht'
  simpa only [program, start, done, hfinal] using h

end TapeHornerTake
end DepthThreeLowerBound

end OAI
