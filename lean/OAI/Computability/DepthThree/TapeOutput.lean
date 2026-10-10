import OAI.Computability.DepthThree.TapeStoreRepresentation

namespace OAI

namespace DepthThreeLowerBound
namespace TapeOutput

open TapeMultiProgram TapeRouting

abbrev State := TapeArray.State ⊕ Bool

def haltProgram : TapeMultiProgram Bool := fun _ _ => none

def acceptFlag : TapeArray.State → Bool
  | .done b => !b
  | _ => false

def program : TapeMultiProgram State :=
  joinCode (TapeArray.code TapeRegister.indexA TapeRegister.accumBits id)
    haltProgram acceptFlag

def start : State := .inl .start
def done (answer : Bool) : State := .inr answer

@[simp] theorem program_done (answer : Bool) (h : TapeHeads) :
    program (done answer) h = none := rfl

theorem runs_output (σ : TapeStore) (b : Bool) (tail : List Bool)
    (hi : σ TapeRegister.indexA = [])
    (ha : σ TapeRegister.accumBits = b :: tail) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (!b)) (storeTapes σ)) 5 := by
  have hr := TapeProductTerm.read_at
    (index := TapeRegister.indexA) (array := TapeRegister.accumBits)
    (by decide) (storeTapes σ) [] tail b
    (by simp [storeTapes, TapeUnary.counterTape, hi])
    (by simp [storeTapes, ha])
  have hh := join_runs (TapeArray.code TapeRegister.indexA TapeRegister.accumBits id)
    haltProgram acceptFlag hr rfl
    (RunsIn.refl haltProgram.step (cfg (!b) (storeTapes σ)))
  simpa only [State, program, start, done, acceptFlag, List.length_nil, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero] using hh

end TapeOutput
end DepthThreeLowerBound

end OAI
