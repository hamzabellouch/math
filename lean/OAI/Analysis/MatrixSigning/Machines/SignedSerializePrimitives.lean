import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FixedPositiveSerializer
import OAI.Analysis.MatrixSigning.Encoding.WireMagnitude
import OAI.Analysis.MatrixSigning.Arithmetic.CanonicalSubtraction

namespace OAI

namespace KS.W01.SignedSerializePrimitives
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_other)

def pairMachine : KS.W29.BinaryMachine := KS.W28.PositiveWireSerializer.machine.withEntry (0 : Fin 5)

def pairProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 pairMachine ports)

theorem pair_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) :
    RunSpec (pairProgram ports) (registers ports spare xs ys zs)
      (registers ports spare [] [] ((frame xs ++ frame ys).reverse ++ zs))
      (2 * xs.length + 2 * ys.length + 2) := by
  intro bits hbits
  change (lift3 pairMachine ports).run
    ⟨some (0 : Fin 5), registers ports spare xs ys zs⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, registers ports spare xs ys zs⟩ : Config k 5) =
        KS.W28.PositiveWireSerializer.cfg (some 0) xs ys zs := by
      change KS.W29.Config.mk _ (fun j => registers ports spare xs ys zs (ports j)) =
        KS.W29.Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> simp
    erw [hp]
    change (KS.W28.PositiveWireSerializer.machine.withEntry (0 : Fin 5)).run _ bits = _
    erw [KS.W29.BinaryMachine.withEntry_run,
      KS.W28.PositiveWireSerializer.run_num xs ys zs bits hbits]
    change KS.W29.Config.mk none
      (KS.W28.PositiveWireSerializer.cfg none [] [] ((frame xs ++ frame ys).reverse ++ zs)).«stacks» = _
    congr 1
    funext j
    fin_cases j <;> simp [KS.W28.PositiveWireSerializer.cfg]
  · intro j hj
    change registers ports spare [] [] ((frame xs ++ frame ys).reverse ++ zs) j =
      registers ports spare xs ys zs j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

def subtractProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W19.CanonicalSubtraction.machine ports)

theorem decrement_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs : List Bool) :
    RunSpec (subtractProgram ports) (registers ports spare xs [true] [])
      (registers ports spare [] (WireMagnitude.decrement xs) [])
      (2 * (max xs.length 1 + 1)) := by
  intro bits hbits
  let cut := max xs.length 1 + 1
  have ht : (bits.take cut).length = max xs.length ([true] : List Bool).length + 1 := by
    simp only [List.length_cons, List.length_nil, List.length_take]
    change min cut bits.length = cut
    apply Nat.min_eq_left
    dsimp [cut]
    omega
  have hd : (bits.drop cut).length = max xs.length ([true] : List Bool).length + 1 := by
    simp only [List.length_drop, List.length_cons, List.length_nil]
    dsimp [cut]
    omega
  change (lift3 KS.W19.CanonicalSubtraction.machine ports).run
    ⟨some KS.W19.CanonicalSubtraction.machine.initial,
      registers ports spare xs [true] []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some KS.W19.CanonicalSubtraction.machine.initial,
          registers ports spare xs [true] []⟩ :
            Config k KS.W19.CanonicalSubtraction.machine.states) =
        KS.W29.Sequential.liftLeft KS.W19.BinarySubtractor.machine KS.W19.BinaryTrimMachine.machine
          (KS.W19.BinarySubtractor.cfg (some 0) xs [true] []) := by
      change KS.W29.Config.mk _ (fun j => registers ports spare xs [true] [] (ports j)) =
        KS.W29.Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> simp [KS.W19.BinarySubtractor.cfg]
    erw [hp, ← List.take_append_drop cut bits,
      KS.W19.CanonicalSubtraction.run_exact xs [true] _ _ ht hd]
    change KS.W29.Config.mk none
      (KS.W19.BinaryTrimMachine.cfg none []
        (Computability.encodeNat (KS.W19.bitsValue (KS.W19.subtractBits xs [true] false))) []).«stacks» = _
    congr 1
    funext j
    fin_cases j <;> simp [KS.W19.BinaryTrimMachine.cfg,
      WireMagnitude.decrement, KS.W19.trimBits_eq_encodeNat]
  · intro j hj
    change registers ports spare [] (WireMagnitude.decrement xs) [] j =
      registers ports spare xs [true] [] j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

end KS.W01.SignedSerializePrimitives

end OAI
