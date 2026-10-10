import OAI.Computability.DepthThree.TapePowerSearch

namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameterSearch

open TapeMultiProgram TapeRouting TapeUnary TapePowerSearch

private theorem erase_output (k : ℕ) (R : Registers) (σ : TapeStore) (c : ℕ)
    (ho : σ (R 0) = []) (hd : σ (R 3) = []) :
    RunsIn (TapeErase.code (TapePower.resultRegister k (R 0) (R 3))).step
      (cfg TapeErase.State.start (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
        (candidateStore R σ c) c)))
      (cfg TapeErase.State.done (storeTapes (candidateStore R σ c))) (2 * c ^ k + 5) := by
  have h := TapeStoreRuns.erase (TapePower.resultRegister k (R 0) (R 3))
    (TapePowerCompare.outputStore k (R 0) (R 3) (candidateStore R σ c) c)
  have ho' : candidateStore R σ c (R 0) = [] := by
    simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho
  have hd' : candidateStore R σ c (R 3) = [] := by
    simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd
  simpa only [TapePowerCompare.outputStore_result, List.length_replicate,
    TapePowerCompare.outputStore_clear k (R 0) (R 3) (candidateStore R σ c) c ho' hd'] using h

private theorem decrement_candidate (R : Registers) (σ : TapeStore) (c : ℕ) :
    RunsIn (decProgram (R 1)).step
      (cfg DecState.start (storeTapes (candidateStore R σ (c + 1))))
      (cfg (DecState.done true) (storeTapes (candidateStore R σ c))) 4 := by
  have h := decrement_cons (R 1) (storeTapes (candidateStore R σ (c + 1)))
    (List.replicate c true) true (by
      simp [storeTapes, candidateStore, List.replicate_succ])
  have he : Function.update (storeTapes (candidateStore R σ (c + 1))) (R 1)
      (wordTape (List.replicate c true)) = storeTapes (candidateStore R σ c) := by
    rw [← storeTapes_update]
    simp [candidateStore]
  simpa only [he] using h

abbrev CubeState := TapePowerSearch.State 3 ⊕ TapeErase.State

def cubeProgram (R : Registers) : TapeMultiProgram CubeState :=
  joinCode (TapePowerSearch.program 3 false continueLt R)
    (TapeErase.code (TapePower.resultRegister 3 (R 0) (R 3)))
    (fun _ => TapeErase.State.start)

def cubeStart : CubeState := .inl (TapePowerSearch.start 3)
def cubeDone : CubeState := .inr .done

def cubeCost (d : ℕ) : ℕ :=
  TapePowerSearch.cost 3 false (d ^ 2) (hashDimension d) 0 + 1 +
    (2 * (hashDimension d) ^ 3 + 5)

theorem runs_cube (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate (d ^ 2) true) :
    RunsIn (cubeProgram R).step
      (cfg cubeStart (storeTapes (candidateStore R σ 0)))
      (cfg cubeDone (storeTapes (candidateStore R σ (hashDimension d))))
      (cubeCost d) := by
  have hc := TapePowerSearch.runs_cube R σ d ho hs hd ht
  have he := erase_output 3 R σ (hashDimension d) ho hd
  exact join_runs _ _ _ hc rfl he

@[simp] theorem cube_done (R : Registers) (h : TapeHeads) :
    cubeProgram R cubeDone h = none := rfl

abbrev DecreaseState := DecState ⊕ DecState

def decreaseProgram (R : Registers) : TapeMultiProgram DecreaseState :=
  joinCode (decProgram (R 1)) (decProgram (R 1)) (fun _ => DecState.start)

def decreaseStart : DecreaseState := .inl .start
def decreaseDone : DecreaseState := .inr (.done true)

theorem runs_decrease (R : Registers) (σ : TapeStore) (c : ℕ) :
    RunsIn (decreaseProgram R).step
      (cfg decreaseStart (storeTapes (candidateStore R σ (c + 2))))
      (cfg decreaseDone (storeTapes (candidateStore R σ c))) 9 := by
  have h₁ := decrement_candidate R σ (c + 1)
  have h₂ := decrement_candidate R σ c
  have h := join_runs (decProgram (R 1)) (decProgram (R 1))
    (fun _ => DecState.start) h₁ rfl h₂
  have he : c + 1 + 1 = c + 2 := by omega
  simpa only [decreaseProgram, decreaseStart, decreaseDone, he] using h

abbrev CleanupState := TapeErase.State ⊕ DecreaseState

def cleanupProgram (R : Registers) : TapeMultiProgram CleanupState :=
  joinCode (TapeErase.code (TapePower.resultRegister 6 (R 0) (R 3)))
    (decreaseProgram R) (fun _ => decreaseStart)

def cleanupStart : CleanupState := .inl .start
def cleanupDone : CleanupState := .inr decreaseDone

theorem runs_cleanup (R : Registers) (σ : TapeStore) (c : ℕ)
    (ho : σ (R 0) = []) (hd : σ (R 3) = []) :
    RunsIn (cleanupProgram R).step
      (cfg cleanupStart (storeTapes (TapePowerCompare.outputStore 6 (R 0) (R 3)
        (candidateStore R σ (c + 2)) (c + 2))))
      (cfg cleanupDone (storeTapes (candidateStore R σ c)))
      (2 * (c + 2) ^ 6 + 5 + 1 + 9) := by
  have he := erase_output 6 R σ (c + 2) ho hd
  have hd := runs_decrease R σ c
  exact join_runs _ _ _ he rfl hd

abbrev SixthState := TapePowerSearch.State 6 ⊕ CleanupState

def sixthProgram (R : Registers) : TapeMultiProgram SixthState :=
  joinCode (TapePowerSearch.program 6 true continueLe R) (cleanupProgram R)
    (fun _ => cleanupStart)

def sixthStart : SixthState := .inl (TapePowerSearch.start 6)
def sixthDone : SixthState := .inr cleanupDone

def sixthCost (d : ℕ) : ℕ :=
  TapePowerSearch.cost 6 true d (independenceOrder d / 2 + 1) 0 + 1 +
    (2 * (independenceOrder d + 2) ^ 6 + 5 + 1 + 9)

theorem runs_sixth (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate d true) :
    RunsIn (sixthProgram R).step
      (cfg sixthStart (storeTapes (candidateStore R σ 0)))
      (cfg sixthDone (storeTapes (candidateStore R σ (independenceOrder d))))
      (sixthCost d) := by
  have hs := TapePowerSearch.runs_sixth_boundary R σ d ho hs hd ht
  have hc := runs_cleanup R σ (independenceOrder d) ho hd
  exact join_runs _ _ _ hs rfl hc

@[simp] theorem sixth_done (R : Registers) (h : TapeHeads) :
    sixthProgram R sixthDone h = none := rfl

end TapeParameterSearch
end DepthThreeLowerBound

end OAI
