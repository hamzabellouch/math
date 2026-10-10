import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.UnsignedPairSerializer
import OAI.Analysis.MatrixSigning.Arithmetic.CanonicalSubtraction

namespace OAI

section

namespace KS.W19.FixedSubtraction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def program {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 CanonicalSubtraction.machine ports)

theorem subtract_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) (hsub : bitsValue ys ≤ bitsValue xs) :
    RunSpec (program ports) (registers ports spare xs ys [])
      (registers ports spare [] (Computability.encodeNat (bitsValue xs - bitsValue ys)) [])
      (2 * (max xs.length ys.length + 1)) := by
  intro bits hb
  let n := max xs.length ys.length + 1
  have hl : (bits.take n).length = n := by simp only [List.length_take, hb]; dsimp [n]; omega
  have hr : (bits.drop n).length = n := by simp only [List.length_drop, hb]; dsimp [n]; omega
  have hcall := CanonicalSubtraction.run_exact xs ys (bits.take n) (bits.drop n) hl hr
  rw [List.take_append_drop] at hcall
  have hnum := subtractBits_correct xs ys false (by simpa only [digit_false, Nat.add_zero] using hsub)
  have hv : bitsValue (subtractBits xs ys false) = bitsValue xs - bitsValue ys := by
    simp only [digit_false, Nat.add_zero] at hnum
    omega
  change (lift3 CanonicalSubtraction.machine ports).run
    ⟨some (0 : Fin 4), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (0 : Fin 4), registers ports spare xs ys []⟩ : Config k 4) =
        KS.W29.Sequential.liftLeft BinarySubtractor.machine BinaryTrimMachine.machine
          (BinarySubtractor.cfg (some 0) xs ys []) := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 4)))
      funext j
      fin_cases j <;> simp [BinarySubtractor.cfg]
    have hr' := congrArg (fun c => CanonicalSubtraction.machine.run c bits) hp
    refine hr'.trans (hcall.trans ?_)
    apply congrArg₂ KS.W29.Config.mk
    · rfl
    · funext j
      fin_cases j <;> simp [BinaryTrimMachine.cfg, hv]
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

end KS.W19.FixedSubtraction

end

end OAI
