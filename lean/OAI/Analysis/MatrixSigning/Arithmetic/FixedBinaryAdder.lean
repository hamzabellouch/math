import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAdderCompose

namespace OAI

section

namespace KS.W01.FixedBinaryAdder
open KS.W29 KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def result (xs ys : List Bool) : List Bool := BinaryAdder.addBits false xs ys

def ticks (xs ys : List Bool) : ℕ := max xs.length ys.length + 1 + ((result xs ys).length + 1)

theorem run_bits (xs ys bits : List Bool) (hlen : bits.length = ticks xs ys) :
    BinaryAdder.normalizedMachine.run
      ⟨some BinaryAdder.normalizedMachine.initial, ![xs, ys, []]⟩ bits =
        ⟨none, ![[], result xs ys, []]⟩ := by
  let cut := max xs.length ys.length + 1
  have hfirst : (bits.take cut).length = max xs.length ys.length + 1 := by
    simp only [List.length_take]
    change min cut bits.length = cut
    apply Nat.min_eq_left
    dsimp [cut]
    unfold ticks at hlen
    omega
  have hsecond : (bits.drop cut).length = (result xs ys).length + 1 := by
    simp only [List.length_drop]
    dsimp [cut]
    unfold ticks at hlen
    omega
  have h := BinaryAdder.run_normalized xs ys (bits.take cut) (bits.drop cut) hfirst hsecond
  rw [List.take_append_drop] at h
  have hi : (⟨some BinaryAdder.normalizedMachine.initial,![xs,ys,[]]⟩ :
      KS.W29.Config BinaryAdder.normalizedMachine.states) =
      Sequential.liftLeft BinaryAdder.machine NormalizeOutput.machine (BinaryAdder.cfg (some 0) xs ys []) := by
    apply congrArg₂ KS.W29.Config.mk
    · rfl
    · funext j; fin_cases j <;> rfl
  rw [hi,h]
  apply congrArg₂ KS.W29.Config.mk
  · rfl
  · funext j; fin_cases j <;> rfl

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 BinaryAdder.normalizedMachine ports)

def output {k : ℕ} (ports : Fin 3 ↪ Fin k) (store : Fin k → List Bool)
    (xs ys : List Bool) : Fin k → List Bool :=
  Function.update (Function.update store (ports 0) []) (ports 1) (result xs ys)

theorem runSpec {k : ℕ} (ports : Fin 3 ↪ Fin k) (store : Fin k → List Bool)
    (xs ys : List Bool) (hx : store (ports 0) = xs) (hy : store (ports 1) = ys)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports) store (output ports store xs ys) (ticks xs ys) := by
  intro bits hbits
  change (lift3 BinaryAdder.normalizedMachine ports).run
    ⟨some BinaryAdder.normalizedMachine.initial, store⟩ bits = _
  apply lift3_run_eq
  · have hi : project ports
        (⟨some BinaryAdder.normalizedMachine.initial, store⟩ :
          Config k BinaryAdder.normalizedMachine.states) =
        ⟨some BinaryAdder.normalizedMachine.initial, ![xs, ys, []]⟩ := by
      change KS.W29.Config.mk _ (fun j => store (ports j)) = KS.W29.Config.mk _ _
      congr 1
      funext j
      fin_cases j
      · exact hx
      · exact hy
      · exact hscratch
    erw [hi, run_bits xs ys bits hbits]
    congr 1
    funext j
    fin_cases j <;> simp [output, Function.update, ports.injective.eq_iff, hscratch]
  · intro j hj
    simp [output, Function.update, hj 0, hj 1]

theorem runSpec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k) (store : Fin k → List Bool)
    (xs ys : List Bool) (hx : store (ports 0) = xs) (hy : store (ports 1) = ys)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports) store (output ports store xs ys) (2 * (xs.length + ys.length) + 3) := by
  apply (runSpec ports store xs ys hx hy hscratch).mono
  exact BinaryAdder.normalized_transition_bound xs ys

theorem result_value (xs ys : List Bool) :
    KS.W19.bitsValue (result xs ys) = KS.W19.bitsValue xs + KS.W19.bitsValue ys := by
  simpa [result, KS.W19.digit] using BinaryAdder.addBits_correct false xs ys

end KS.W01.FixedBinaryAdder

end

end OAI
