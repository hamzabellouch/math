import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryTrimMachine
import OAI.Analysis.MatrixSigning.Arithmetic.SubtractorSequential

namespace OAI

section

namespace KS.W19.CanonicalSubtraction
open KS.W29 KS.W29.Sequential

def machine : BinaryMachine := Sequential.compose BinarySubtractor.machine BinaryTrimMachine.machine

theorem run_exact (xs ys first second : List Bool)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = max xs.length ys.length + 1) :
    machine.run
      (liftLeft BinarySubtractor.machine BinaryTrimMachine.machine
        (BinarySubtractor.cfg (some 0) xs ys [])) (first ++ second) =
      liftRight BinarySubtractor.machine BinaryTrimMachine.machine
        (BinaryTrimMachine.cfg none []
          (Computability.encodeNat (bitsValue (subtractBits xs ys false))) []) := by
  unfold machine
  have hhalt : HaltsAfter BinarySubtractor.machine
      (BinarySubtractor.cfg (some 0) xs ys []) first := by
    simpa only [BinarySubtractor.borrowState, Bool.false_eq_true, ↓reduceIte] using
      BinarySubtractor.haltsAfter_sub false xs ys [] first hfirst
  rw [run_compose BinarySubtractor.machine BinaryTrimMachine.machine
    (BinarySubtractor.cfg (some 0) xs ys []) first second hhalt]
  have hrun := BinarySubtractor.run_sub false xs ys [] first hfirst
  change BinarySubtractor.machine.run (BinarySubtractor.cfg (some 0) xs ys []) first = _ at hrun
  rw [hrun]
  change liftRight BinarySubtractor.machine BinaryTrimMachine.machine
    (BinaryTrimMachine.machine.run
      (BinaryTrimMachine.cfg (some 0) [] [] ((subtractBits xs ys false).reverse ++ [])) second) = _
  simp only [List.append_nil]
  rw [BinaryTrimMachine.run_payload [] (subtractBits xs ys false) second
    (by simpa only [subtractBits_length] using hsecond)]

theorem run_correct (xs ys first second : List Bool) (hsub : bitsValue ys ≤ bitsValue xs)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = max xs.length ys.length + 1) :
    let result := machine.run
      (liftLeft BinarySubtractor.machine BinaryTrimMachine.machine
        (BinarySubtractor.cfg (some 0) xs ys [])) (first ++ second)
    result.state = none ∧ result.«stacks» 0 = [] ∧ result.«stacks» 2 = [] ∧
      result.«stacks» 1 = Computability.encodeNat (bitsValue xs - bitsValue ys) := by
  have hc := subtractBits_correct xs ys false (by simpa using hsub)
  have hv : bitsValue (subtractBits xs ys false) = bitsValue xs - bitsValue ys := by
    simp only [digit_false, Nat.add_zero] at hc
    omega
  dsimp only
  rw [run_exact xs ys first second hfirst hsecond]
  refine ⟨rfl, rfl, rfl, ?_⟩
  change Computability.encodeNat (bitsValue (subtractBits xs ys false)) = _
  rw [hv]

theorem run_encodedNat (n m : ℕ) (hmn : m ≤ n) (first second : List Bool)
    (hfirst : first.length = max (Nat.size n) (Nat.size m) + 1)
    (hsecond : second.length = max (Nat.size n) (Nat.size m) + 1) :
    let result := machine.run
      (liftLeft BinarySubtractor.machine BinaryTrimMachine.machine
        (BinarySubtractor.cfg (some 0) (Computability.encodeNat n) (Computability.encodeNat m) []))
      (first ++ second)
    result.state = none ∧ result.«stacks» 0 = [] ∧ result.«stacks» 2 = [] ∧
      result.«stacks» 1 = Computability.encodeNat (n - m) := by
  simpa only [bitsValue_encodeNat] using
    run_correct (Computability.encodeNat n) (Computability.encodeNat m) first second
      (by simpa only [bitsValue_encodeNat] using hmn)
      (by simpa only [encodeNat_length_eq_size] using hfirst)
      (by simpa only [encodeNat_length_eq_size] using hsecond)

theorem transition_bound (n m : ℕ) :
    2 * (max (Nat.size n) (Nat.size m) + 1) ≤ 2 * (Nat.size n + Nat.size m + 1) := by omega

end KS.W19.CanonicalSubtraction

end

end OAI
