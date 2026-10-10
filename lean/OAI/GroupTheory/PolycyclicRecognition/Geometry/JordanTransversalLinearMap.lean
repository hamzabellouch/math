import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleKernelProjection
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # The invertible leading term for a general Jordan Lang transversal

Only the moving part of the semisimple operator is inverted. Its commuting
unipotent factor is a nilpotent perturbation of this invertible leading term.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [AddCommGroup L] [Module ℝ L] [FiniteDimensional ℝ L]

theorem jordan_transversal_linear_bijective
    (S U : Module.End ℝ L) (hS : S.IsSemisimple)
    (hU : IsNilpotent (U - 1)) (hSU : Commute S U) :
    let B := S - 1
    let hB := semisimple_sub_one S hS
    let P := semisimpleKernelProjection B hB
    Function.Bijective (((S * U - 1) * (1 - P) + P : Module.End ℝ L) : L → L) := by
  let B := S - 1
  have hB : B.IsSemisimple := semisimple_sub_one S hS
  let P := semisimpleKernelProjection B hB
  let Q : Module.End ℝ L := 1 - P
  let E : Module.End ℝ L := B + P
  let N : Module.End ℝ L := S * (U - 1) * Q
  have hPS : Commute P S := semisimpleKernelProjection_commute B S hB
    ((Commute.refl S).sub_left (Commute.one_left S))
  have hPU : Commute P U := semisimpleKernelProjection_commute B U hB
    (hSU.sub_left (Commute.one_left U))
  have hBP : B * P = 0 := by
    apply LinearMap.ext
    intro x
    exact semisimpleKernelProjection_mem B hB x
  have hSP : S * P = P := by
    have hh : S * P - P = 0 := by simpa only [B, sub_mul, one_mul] using hBP
    exact sub_eq_zero.mp hh
  have hQd : Commute Q (U - 1) :=
    ((Commute.one_left U).sub_left hPU).sub_right (Commute.one_right Q)
  have hQS : Commute Q S := (Commute.one_left S).sub_left hPS
  have hSd : Commute S (U - 1) := hSU.sub_right (Commute.one_right S)
  have hN : IsNilpotent N :=
    (hQS.symm.mul_left hQd.symm).isNilpotent_mul_right
      (hSd.isNilpotent_mul_left hU)
  have hES : Commute E S :=
    ((Commute.refl S).sub_left (Commute.one_left S)).add_left hPS
  have hEU : Commute E U := (hSU.sub_left (Commute.one_left U)).add_left hPU
  have hEP : Commute E P :=
    (hPS.symm.sub_left (Commute.one_left P)).add_left (Commute.refl P)
  have hEN : Commute E N :=
    (hES.mul_right (hEU.sub_right (Commute.one_right E))).mul_right
      ((Commute.one_right E).sub_right hEP)
  have hE : IsUnit E := (Module.End.isUnit_iff E).mpr
    (semisimple_add_kernelProjection_bijective B hB)
  have hsum : (S * U - 1) * Q + P = E + N := by
    dsimp only [E, N, B, Q]
    noncomm_ring [hSP]
  change Function.Bijective (((S * U - 1) * Q + P : Module.End ℝ L) : L → L)
  rw [hsum]
  exact (Module.End.isUnit_iff _).mp (hN.isUnit_add_left_of_commute hE hEN.symm)

end PolycyclicRecognition

end

end OAI
