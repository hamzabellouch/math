import OAI.Computability.DepthThree.TapeRouting
import OAI.Computability.DepthThree.TapeUnary
import OAI.Computability.DepthThree.TapeCopy
import Lean.Elab.Tactic.Omega

namespace OAI

universe uDepth1 uDepth2

namespace DepthThreeLowerBound
namespace TapeArithmetic

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

theorem update_onPair_src {α : Type uDepth1} (src dst : TapeRegister)
    (T : TapeRegister → α) (s d s' : α) :
    Function.update (onPair src dst T s d) src s' = onPair src dst T s' d := by
  funext r
  by_cases h : r = src
  · subst r
    simp
  · simp [Function.update, onPair, h]

theorem update_onPair_dst {α : Type uDepth2} {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeRegister → α) (s d d' : α) :
    Function.update (onPair src dst T s d) dst d' = onPair src dst T s d' := by
  funext r
  by_cases hs : r = src
  · subst r
    simp [Function.update, onPair, hne]
  · by_cases hd : r = dst
    · subst r
      simp [Function.update, onPair, Ne.symm hne]
    · simp [Function.update, onPair, hs, hd]

def decPositive : DecState → Bool
  | .done b => b
  | _ => false

abbrev AddState := LoopState DecState IncState

def addProgram (counter destination : TapeRegister) : TapeMultiProgram AddState :=
  loopCode (decProgram counter) (incProgram destination)
    DecState.start IncState.start decPositive

def addStart : AddState := loopTest DecState.start
def addDone : AddState := loopDone

theorem runs_add {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (addProgram counter destination).step
      (cfg addStart (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg addDone (onPair counter destination T (counterTape 0) (counterTape (m + n))))
      (8 * n + 3) := by
  induction n generalizing m with
  | zero =>
      have hdec := decrement_empty counter
        (onPair counter destination T (counterTape 0) (counterTape m)) (by
          simp [counterTape])
      have he := loop_exit (decProgram counter) (incProgram destination)
        DecState.start IncState.start decPositive hdec rfl rfl
      simpa only [addProgram, addStart, addDone, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero] using he
  | succ n ih =>
      have hdec := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (counterTape m))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hdec
      have hinc := increment destination
        (onPair counter destination T (counterTape n) (counterTape m)) m (by
          simp [hne])
      simp only [update_onPair_dst hne] at hinc
      have hit := loop_iter (decProgram counter) (incProgram destination)
        DecState.start IncState.start decPositive hdec rfl rfl hinc rfl
      have hrest := ih (m + 1)
      have hall := hit.trans hrest
      have hacc : m + 1 + n = m + (n + 1) := by omega
      have htime : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
      simpa only [addProgram, addStart, addDone, hacc, htime] using hall

@[simp] theorem add_done (counter destination : TapeRegister) (h : TapeHeads) :
    addProgram counter destination addDone h = none := rfl

end TapeArithmetic
end DepthThreeLowerBound

end OAI
