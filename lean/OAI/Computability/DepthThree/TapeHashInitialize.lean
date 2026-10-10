import OAI.Computability.DepthThree.TapeStoreRepresentation

namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashInitialize

open TapeMultiProgram TapeRouting TapeRegister

abbrev State := TapeCopy.State ⊕ TapeFill.FillState

def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree scratchA) (TapeFill.fillProgram scratchA hashBits false)
    (fun _ => TapeFill.fillStart)

def start : State := .inl TapeCopy.State.start
def done : State := .inr TapeFill.fillDone

theorem runs_initialize (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hs : σ scratchA = []) (hh : σ hashBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.replicate r false))))
      (10 * r + 8) := by
  let τ := Function.update σ scratchA (σ ringDegree)
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ scratchA) σ hs
  have hfill := TapeStoreRuns.fill (by decide : scratchA ≠ hashBits) false τ r
    (by simp [τ, hr])
  have hall := join_runs (TapeCopy.code ringDegree scratchA)
    (TapeFill.fillProgram scratchA hashBits false) (fun _ => TapeFill.fillStart)
    hcopy rfl hfill
  have hstore : Function.update (Function.update τ scratchA []) hashBits
      (List.replicate r false ++ τ hashBits) =
        Function.update σ hashBits (List.replicate r false) := by
    have hreset : Function.update τ scratchA [] = σ := by
      simp only [τ, Function.update_idem, ← hs, Function.update_eq_self]
    rw [hreset]
    simp [τ, hh, hashBits, scratchA]
  have htime : 2 * r + 4 + 1 + (8 * r + 3) = 10 * r + 8 := by omega
  simpa only [program, start, done, hstore, hr, List.length_replicate, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashInitialize
end DepthThreeLowerBound

end OAI
