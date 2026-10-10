import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.LittleEndianCompare

namespace OAI

section

namespace KS.W28.FixedCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 LittleEndianCompare.machine ports)

def after {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Fin k → List Bool)
    (b : Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then [] else if j = ports 1 then []
  else if j = ports 2 then b :: registerMap j else registerMap j

@[simp] theorem after_left {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) : after ports registerMap b (ports 0) = [] := by
  simp [after]

@[simp] theorem after_right {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) : after ports registerMap b (ports 1) = [] := by
  simp [after, ports.injective.eq_iff]

@[simp] theorem after_result {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) :
    after ports registerMap b (ports 2) = b :: registerMap (ports 2) := by
  simp [after, ports.injective.eq_iff]

theorem after_other {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) (j : Fin k)
    (hj : ∀ i, j ≠ ports i) : after ports registerMap b j = registerMap j := by
  simp [after, hj 0, hj 1, hj 2]

theorem compare_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Fin k → List Bool) :
    RunSpec (program ports) registerMap
      (after ports registerMap (decide
        (KS.W19.bitsValue (registerMap (ports 0)) ≤ KS.W19.bitsValue (registerMap (ports 1)))))
      (max (registerMap (ports 0)).length (registerMap (ports 1)).length + 1) := by
  intro bits hbits
  change (lift3 LittleEndianCompare.machine ports).run ⟨some (0 : Fin 3), registerMap⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, registerMap⟩ : Config k 3) =
        LittleEndianCompare.cfg (some 0) (registerMap (ports 0)) (registerMap (ports 1))
          (registerMap (ports 2)) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 3)))
      funext j
      fin_cases j <;> rfl
    erw [hp]
    have hr := LittleEndianCompare.run_correct (registerMap (ports 0)) (registerMap (ports 1))
      (registerMap (ports 2)) bits hbits
    change LittleEndianCompare.machine.run
      (LittleEndianCompare.cfg (some 0) _ _ _) bits = _ at hr
    erw [hr]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    exact after_other ports registerMap _ j hj

theorem compare_spec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) :
    RunSpec (program ports) registerMap
      (after ports registerMap (decide
        (KS.W19.bitsValue (registerMap (ports 0)) ≤ KS.W19.bitsValue (registerMap (ports 1)))))
      ((registerMap (ports 0)).length + (registerMap (ports 1)).length + 1) := by
  apply (compare_spec ports registerMap).mono
  omega

end KS.W28.FixedCompare

end

end OAI
