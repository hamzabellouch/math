import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Encoding.PositiveWireSerializer
import OAI.Analysis.MatrixSigning.Machines.NormalizeOutput

namespace OAI

section

namespace KS.W28.FixedPositiveSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def registers {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then xs else if j = ports 1 then ys else if j = ports 2 then zs else spare j

@[simp] theorem registers_port {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (i : Fin 3) :
    registers ports spare xs ys zs (ports i) =
      if i = 0 then xs else if i = 1 then ys else zs := by
  fin_cases i <;> simp [registers, ports.injective.eq_iff]

theorem registers_other {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (j : Fin k)
    (hj : ∀ i, j ≠ ports i) : registers ports spare xs ys zs j = spare j := by
  simp [registers, hj 0, hj 1, hj 2]

def emitProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 PositiveWireSerializer.machine ports)

def reverseProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.NormalizeOutput.machine ports)

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (emitProgram ports) (reverseProgram ports)

theorem emit_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (emitProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] [] (PositiveWireSerializer.wire xs ys).reverse)
      (2 * xs.length + 2 * ys.length + 3) := by
  intro bits hbits
  change (lift3 PositiveWireSerializer.machine ports).run
    ⟨some (4 : Fin 5), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 4, registers ports spare xs ys []⟩ : Config k 5) =
        PositiveWireSerializer.cfg (some 4) xs ys [] := by
      change KS.W29.Config.mk (some (4 : Fin 5)) _ = KS.W29.Config.mk (some (4 : Fin 5)) _
      apply congrArg (KS.W29.Config.mk (some (4 : Fin 5)))
      funext j
      simp
    erw [hp, PositiveWireSerializer.run_wire xs ys [] bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare [] [] (PositiveWireSerializer.wire xs ys).reverse j =
      registers ports spare xs ys [] j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

theorem reverse_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (wire : List Bool) :
    RunSpec (reverseProgram ports) (registers ports spare [] [] wire.reverse)
      (registers ports spare [] wire []) (wire.length + 1) := by
  intro bits hbits
  change (lift3 KS.W29.NormalizeOutput.machine ports).run
    ⟨some (2 : Fin 3), registers ports spare [] [] wire.reverse⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some 2, registers ports spare [] [] wire.reverse⟩ : Config k 3) =
        KS.W29.FrameDecoder.config (some 2) [] [] wire.reverse := by
      change KS.W29.Config.mk (some (2 : Fin 3)) _ = KS.W29.Config.mk (some (2 : Fin 3)) _
      apply congrArg (KS.W29.Config.mk (some (2 : Fin 3)))
      funext j
      simp
    erw [hp, KS.W29.NormalizeOutput.run_reversed [] wire bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare [] wire [] j = registers ports spare [] [] wire.reverse j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

theorem serialize_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (program ports) (registers ports spare xs ys [])
      (registers ports spare [] (PositiveWireSerializer.wire xs ys) [])
      (4 * xs.length + 4 * ys.length + 7) := by
  have h := (emit_spec ports spare xs ys).compose
    (reverse_spec ports spare (PositiveWireSerializer.wire xs ys))
  have ht : (2 * xs.length + 2 * ys.length + 3) +
      ((PositiveWireSerializer.wire xs ys).length + 1) =
      4 * xs.length + 4 * ys.length + 7 := by
    rw [PositiveWireSerializer.wire_length]
    omega
  rw [ht] at h
  exact h

theorem positive_rat_serialize_spec {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (q : ℚ) (hq : 0 ≤ q) :
    RunSpec (program ports)
      (registers ports spare (Computability.encodeNat q.num.natAbs)
        (Computability.encodeNat q.den) [])
      (registers ports spare [] (KS.W01.encodeRat q) [])
      (4 * (Computability.encodeNat q.num.natAbs).length +
        4 * (Computability.encodeNat q.den).length + 7) := by
  have hn : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hw : PositiveWireSerializer.wire (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) = KS.W01.encodeRat q := by
    rw [KS.W01.encodeRat, ← hn]
    rfl
  have h := serialize_spec ports spare (Computability.encodeNat q.num.natAbs)
    (Computability.encodeNat q.den)
  rw [hw] at h
  exact h

end KS.W28.FixedPositiveSerializer

end

end OAI
