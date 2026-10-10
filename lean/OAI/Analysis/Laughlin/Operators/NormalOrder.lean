import Mathlib.Tactic.NoncommRing
import OAI.Analysis.Laughlin.Operators.CAR

namespace OAI

namespace Laughlin.Fock

noncomputable def delta {Q : ℕ} (i j : Fin (Q+1)) : ℂ := if i = j then 1 else 0

theorem annihilate_create {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j = delta i j • (1 : Module.End ℂ (Space Q)) -
      create j * annihilate i := by
  exact eq_sub_of_add_eq (mixed_car i j)

theorem normal_order_entry {Q : ℕ} (P R : Module.End ℂ (Space Q))
    (i j k l : Fin (Q+1)) :
    (P * create j * annihilate i) * (create k * annihilate l * R) =
      delta i k • (P * create j * annihilate l * R) -
        P * create j * create k * annihilate i * annihilate l * R := by
  calc
    _ = P * create j * (annihilate i * create k) * annihilate l * R := by
      noncomm_ring
    _ = _ := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring

theorem normal_order_two_inner {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (annihilate b * create d) -
      delta b c • (annihilate a * create d) +
      create c * annihilate b * annihilate a * create d := by
  calc
    _ = annihilate b * (annihilate a * create c) * create d := by noncomm_ring
    _ = delta a c • (annihilate b * create d) -
        (annihilate b * create c) * annihilate a * create d := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b c]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

end Laughlin.Fock

end OAI
