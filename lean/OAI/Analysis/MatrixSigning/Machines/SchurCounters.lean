import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddPrimitives

namespace OAI

section

namespace KS.W07.SchurCounters

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def pushDispatch {k : ℕ} (port : Fin k) (bit : Bool) (_ : Fin 1)
    (_heads : Fin k → Fin 3) (_coin : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = port then .push bit else .stay)⟩

def pushProgram {k : ℕ} (port : Fin k) (bit : Bool) : Program k :=
  ofMachine (compile 0 port port (pushDispatch port bit))

theorem push_spec {k : ℕ} (port : Fin k) (bit : Bool) (before : Fin k → List Bool) :
    RunSpec (pushProgram port bit) before
      (Function.update before port (bit :: before port)) 1 := by
  intro bits hlen
  cases bits with
  | nil => simp at hlen
  | cons coin rest =>
    have hr : rest = [] := by
      apply List.length_eq_zero_iff.mp
      simpa using hlen
    subst rest
    change (compile (0 : Fin 1) port port (pushDispatch port bit)).step
      ⟨some (0 : Fin 1), before⟩ coin = _
    erw [step_compile]
    apply congrArg₂ Config.mk
    · rfl
    · funext j
      by_cases hj : j = port
      · subst j
        simp [pushDispatch, Instruction.action, KS.W29.StackAction.apply]
      · simp [pushDispatch, Instruction.action, KS.W29.StackAction.apply, hj]

def incrementProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (pushProgram (ports 0) true) (KS.W13.RationalAdd.canonicalAddProgram ports)

theorem increment_spec {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (before : Fin k → List Bool) (n : ℕ)
    (hzero : before (ports 0) = []) (hcounter : before (ports 1) = Computability.encodeNat n)
    (hscratch : before (ports 2) = []) :
    RunSpec (incrementProgram ports) before
      (Function.update before (ports 1) (Computability.encodeNat (n + 1)))
      (2 * (Computability.encodeNat n).length + 6) := by
  have h01 : ports 0 ≠ ports 1 := ports.injective.ne (by decide)
  have h02 : ports 0 ≠ ports 2 := ports.injective.ne (by decide)
  have h12 : ports 1 ≠ ports 2 := ports.injective.ne (by decide)
  have hp := push_spec (ports 0) true before
  have hstart : Function.update before (ports 0) (true :: before (ports 0)) =
      registers ports before [true] (Computability.encodeNat n) [] := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      fin_cases i <;> simp [hzero, hcounter, hscratch, Ne.symm h01, Ne.symm h02]
    · have hn : ∀ i, j ≠ ports i := by simpa using hj
      rw [registers_other _ _ _ _ _ _ hn]
      simp [Function.update_of_ne (hn 0)]
  rw [hstart] at hp
  have ha := KS.W13.RationalAdd.canonicalAdd_spec ports before [true]
    (Computability.encodeNat n)
  have hresult : KS.W13.RationalAdd.addResult [true] (Computability.encodeNat n) =
      Computability.encodeNat (n + 1) := by
    simp [KS.W13.RationalAdd.addResult, KS.W19.bitsValue_encodeNat, KS.W19.bitsValue, Nat.add_comm]
  have hend : registers ports before []
      (KS.W13.RationalAdd.addResult [true] (Computability.encodeNat n)) [] =
      Function.update before (ports 1) (Computability.encodeNat (n + 1)) := by
    rw [hresult]
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      fin_cases i <;> simp [hzero, hscratch, h01, Ne.symm h12]
    · have hn : ∀ i, j ≠ ports i := by simpa using hj
      rw [registers_other _ _ _ _ _ _ hn]
      simp [Function.update_of_ne (hn 1)]
  have h := hp.compose ha
  rw [hend] at h
  have ht := KS.W13.RationalAdd.canonicalAddTicks_le [true] (Computability.encodeNat n)
  apply h.mono
  simp only [List.length_singleton] at ht
  omega

end KS.W07.SchurCounters

end

end OAI
