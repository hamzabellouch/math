import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAdder
import OAI.Analysis.MatrixSigning.Machines.FixedCanonicalize

namespace OAI

section

namespace KS.W13.RationalAdd

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def rawAddProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W01.BinaryAdder.machine ports)

def addTrimProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 BinaryTrimMachine.machine ports)

def canonicalAddProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (rawAddProgram ports) (addTrimProgram ports)

def addResult (xs ys : List Bool) : List Bool :=
  Computability.encodeNat (bitsValue xs + bitsValue ys)

def canonicalAddTicks (xs ys : List Bool) : ℕ :=
  (max xs.length ys.length + 1) + ((KS.W01.BinaryAdder.addBits false xs ys).length + 1)

theorem rawAdd_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (rawAddProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] [] (KS.W01.BinaryAdder.addBits false xs ys).reverse)
      (max xs.length ys.length + 1) := by
  intro bits hbits
  change (lift3 KS.W01.BinaryAdder.machine ports).run
    ⟨some (0 : Fin 2), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (0 : Fin 2), registers ports spare xs ys []⟩ : Config k 2) =
        KS.W01.BinaryAdder.cfg (some 0) xs ys [] := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 2)))
      funext i
      fin_cases i <;> simp
    have hr := congrArg (fun c => KS.W01.BinaryAdder.machine.run c bits) hp
    have h := KS.W01.BinaryAdder.run_add false xs ys [] bits hbits
    change KS.W01.BinaryAdder.machine.run (KS.W01.BinaryAdder.cfg (some 0) xs ys []) bits = _ at h
    refine hr.trans (h.trans ?_)
    apply congrArg₂ KS.W29.Config.mk rfl
    funext i
    fin_cases i <;> simp
  · intro j hj
    change registers ports spare [] [] (KS.W01.BinaryAdder.addBits false xs ys).reverse j =
      registers ports spare xs ys [] j
    simp only [registers_other _ _ _ _ _ _ hj]

theorem canonicalAdd_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (canonicalAddProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] (addResult xs ys) []) (canonicalAddTicks xs ys) := by
  have htrim := KS.W19.FixedCanonicalize.trim_spec ports spare []
    (KS.W01.BinaryAdder.addBits false xs ys)
  have h := (rawAdd_spec ports spare xs ys).compose htrim
  have he : bitsValue (KS.W01.BinaryAdder.addBits false xs ys) = bitsValue xs + bitsValue ys := by
    simpa using KS.W01.BinaryAdder.addBits_correct false xs ys
  simpa only [canonicalAddProgram, addTrimProgram, KS.W19.FixedCanonicalize.trimProgram,
    canonicalAddTicks, addResult, he] using h

theorem canonicalAddTicks_le (xs ys : List Bool) :
    canonicalAddTicks xs ys ≤ 2 * (xs.length + ys.length) + 3 := by
  have h := KS.W01.BinaryAdder.addBits_length_le false xs ys
  unfold canonicalAddTicks
  omega

theorem addResult_length_le (xs ys : List Bool) :
    (addResult xs ys).length ≤ max xs.length ys.length + 1 := by
  have hv : bitsValue (KS.W01.BinaryAdder.addBits false xs ys) = bitsValue xs + bitsValue ys := by
    simpa using KS.W01.BinaryAdder.addBits_correct false xs ys
  have ht := trimBits_length_le (KS.W01.BinaryAdder.addBits false xs ys)
  rw [trimBits_eq_encodeNat, hv] at ht
  exact ht.trans (KS.W01.BinaryAdder.addBits_length_le false xs ys)

theorem addResult_canonical (xs ys : List Bool) : CanonicalBits (addResult xs ys) :=
  canonicalBits_encodeNat _

end KS.W13.RationalAdd

end

end OAI
