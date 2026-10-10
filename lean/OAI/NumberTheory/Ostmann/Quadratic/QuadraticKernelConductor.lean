import OAI.NumberTheory.Ostmann.Quadratic.QuadraticReciprocityCharacter

namespace OAI

/-! # Conductor bounds for the signed kernel characters -/

namespace Ostmann

/-- A twist whose conductor is coprime to that of a character cannot remove
any of the latter's conductor. -/
theorem conductor_dvd_conductor_mul {n : ℕ} [NeZero n]
    (χ ψ : DirichletCharacter ℝ n) (hcop : χ.conductor.Coprime ψ.conductor) :
    χ.conductor ∣ (χ * ψ).conductor := by
  have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at h
  exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))

/-- Only the two-part can change when the odd squarefree Jacobi character is
multiplied by a character of level coprime to that odd part. -/
theorem odd_part_dvd_twisted_conductor (N t : ℕ) [NeZero N] [NeZero t]
    (hN : Squarefree N) (hodd : Odd N) (hcop : N.Coprime t)
    (ψ : DirichletCharacter ℝ t) :
    N ∣ (DirichletCharacter.mul (jacobiCharacter N) ψ).conductor := by
  let : NeZero (Nat.lcm N t) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne t)⟩
  let χ' := (jacobiCharacter N).changeLevel (Nat.dvd_lcm_left N t)
  let ψ' := ψ.changeLevel (Nat.dvd_lcm_right N t)
  have hχ : χ'.conductor = N := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact jacobiCharacter_squarefree_primitive N hN hodd
  have hψ : ψ'.conductor ∣ t := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact ψ.conductor_dvd_level
  have hc : χ'.conductor.Coprime ψ'.conductor := by
    rw [hχ]
    exact hcop.of_dvd_right hψ
  change N ∣ (χ' * ψ').conductor
  simpa only [hχ] using conductor_dvd_conductor_mul χ' ψ' hc

theorem signedOddKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedOddKernelCharacter N negative).conductor ∧
    (signedOddKernelCharacter N negative).conductor ≤ 4 * N := by
  let : NeZero (Nat.lcm N 4) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 4 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 2
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 4)))
      (signedOddKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 4)).trans_eq (Nat.mul_comm N 4))

theorem signedEvenKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedEvenKernelCharacter N negative).conductor ∧
    (signedEvenKernelCharacter N negative).conductor ≤ 8 * N := by
  let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 8 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 3
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 8)))
      (signedEvenKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 8)).trans_eq (Nat.mul_comm N 8))

end Ostmann

end OAI
