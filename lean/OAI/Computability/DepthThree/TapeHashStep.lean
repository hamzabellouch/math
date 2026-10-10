import OAI.Computability.DepthThree.TapeNaturalAccess

namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashStep

open TapeMultiProgram TapeRouting TapeUnary TapeRegister

abbrev State := TapeProductTerm.State ⊕ IncState

def program : TapeMultiProgram State :=
  joinCode (TapeProductTerm.program indexA keyBits indexB dataBits indexC hashBits)
    (incProgram indexA) (fun _ => IncState.start)

def start : State := .inl TapeProductTerm.start
def done : State := .inr IncState.done

def resultStore (σ : TapeStore) (i j : ℕ) : TapeStore :=
  Function.update (Function.update σ hashBits
    (xorListAt (σ hashBits) i ((σ keyBits).getD (i + j) false && (σ dataBits).getD j false)))
    indexA (List.replicate (i + j + 1) true)

theorem runs_step (σ : TapeStore) (i j : ℕ)
    (ha : σ indexA = List.replicate (i + j) true)
    (hb : σ indexB = List.replicate j true)
    (hc : σ indexC = List.replicate i true)
    (hkey : i + j < (σ keyBits).length)
    (hdata : j < (σ dataBits).length) (hout : i < (σ hashBits).length) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ i j))) (4 * i + 4 * j + 17) := by
  let τ := Function.update σ hashBits
    (xorListAt (σ hashBits) i ((σ keyBits).getD (i + j) false && (σ dataBits).getD j false))
  have hterm := TapeNaturalAccess.productTerm indexA keyBits indexB dataBits indexC hashBits
    (by decide) (by decide) (by decide) σ (i + j) j i ha hb hc hkey hdata hout
  have hinc := increment indexA (storeTapes τ) (i + j) (by
    simp [τ, ha, counterTape, indexA, hashBits])
  have hinc' : RunsIn (incProgram indexA).step (cfg IncState.start (storeTapes τ))
      (cfg IncState.done (storeTapes (resultStore σ i j))) 2 := by
    simpa only [resultStore, τ, storeTapes_update, counterTape] using hinc
  have hall := join_runs
    (TapeProductTerm.program indexA keyBits indexB dataBits indexC hashBits)
    (incProgram indexA) (fun _ => IncState.start) hterm rfl hinc'
  have htime : 2 * ((i + j) + j + i) + 14 + 1 + 2 = 4 * i + 4 * j + 17 := by omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashStep
end DepthThreeLowerBound

end OAI
