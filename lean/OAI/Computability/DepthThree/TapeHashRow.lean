import OAI.Computability.DepthThree.TapeHashInner

namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashRow

open TapeMultiProgram TapeRouting TapeRegister

abbrev RunState := TapeCopy.State ⊕ TapeHashInner.State
abbrev ClearState := RunState ⊕ TapeErase.State
abbrev State := ClearState ⊕ TapeErase.State

def runProgram : TapeMultiProgram RunState :=
  joinCode (TapeCopy.code indexC indexA) TapeHashInner.program
    (fun _ => TapeHashInner.start)

def clearProgram : TapeMultiProgram ClearState :=
  joinCode runProgram (TapeErase.code indexA) (fun _ => TapeErase.State.start)

def program : TapeMultiProgram State :=
  joinCode clearProgram (TapeErase.code indexB) (fun _ => TapeErase.State.start)

def start : State := .inl (.inl (.inl TapeCopy.State.start))
def done : State := .inr TapeErase.State.done

def resultStore (σ : TapeStore) (i d : ℕ) : TapeStore :=
  Function.update σ hashBits
    (hashUpdateRow (σ keyBits) (σ dataBits) i (List.range d) (σ hashBits))

theorem runs_row (σ : TapeStore) (i d r : ℕ)
    (hi : i < r) (hd : σ dataLength = List.replicate d true)
    (ha : σ indexA = []) (hb : σ indexB = [])
    (hc : σ indexC = List.replicate i true)
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ i d)))
      (d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25) := by
  let τ := Function.update σ indexA (σ indexC)
  let τ₁ := TapeHashInner.progressStore τ i d
  let τ₂ := Function.update τ₁ indexA []
  let τ₃ := Function.update τ₂ indexB []
  have hcopy := TapeStoreRuns.copy (by decide : indexC ≠ indexA) σ ha
  have hinner := TapeHashInner.runs_inner τ i d r hi
    (by simp [τ, hd, dataLength, indexA])
    (by simp [τ, hc])
    (by simp [τ, hb, indexA, indexB])
    (by simp [τ, hc, indexA, indexC])
    (by simpa [τ, indexA, keyBits] using hkey)
    (by simpa [τ, indexA, dataBits] using hdata)
    (by simpa [τ, indexA, hashBits] using hout)
  have hrun := join_runs (TapeCopy.code indexC indexA) TapeHashInner.program
    (fun _ => TapeHashInner.start) hcopy rfl hinner
  have heraseA := TapeStoreRuns.erase indexA τ₁
  have hclear := join_runs runProgram (TapeErase.code indexA)
    (fun _ => TapeErase.State.start) hrun rfl heraseA
  have heraseB := TapeStoreRuns.erase indexB τ₂
  have hall := join_runs clearProgram (TapeErase.code indexB)
    (fun _ => TapeErase.State.start) hclear rfl heraseB
  have hstore : τ₃ = resultStore σ i d := by
    funext q
    by_cases hB : q = indexB
    · subst q
      simp [τ₃, resultStore, hb, indexB, hashBits]
    · by_cases hA : q = indexA
      · subst q
        simp [τ₃, τ₂, resultStore, ha, indexA, indexB, hashBits]
      · by_cases hH : q = hashBits
        · subst q
          simp [τ₃, τ₂, τ₁, TapeHashInner.progressStore, τ, resultStore,
            indexA, indexB, hashBits, keyBits, dataBits]
        · simp [τ₃, τ₂, τ₁, TapeHashInner.progressStore, τ, resultStore, hB, hA, hH]
  have hlenC : (σ indexC).length = i := by simp [hc]
  have hlenA : (τ₁ indexA).length = i + d := by
    simp [τ₁, TapeHashInner.progressStore, indexA, indexB]
  have hlenB : (τ₂ indexB).length = d := by
    simp [τ₂, τ₁, TapeHashInner.progressStore, indexA, indexB]
  have htime : ((2 * i + 4 + 1 + (d * (4 * i + 8 * d + 29) + 4 * d + 8)) +
      1 + (2 * (i + d) + 5)) + 1 + (2 * d + 5) =
      d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 := by ring
  have hall' : RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes τ₃))
      (d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25) := by
    simpa only [program, start, done, hlenC, hlenA, hlenB, htime] using hall
  simpa only [hstore] using hall'

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashRow
end DepthThreeLowerBound

end OAI
