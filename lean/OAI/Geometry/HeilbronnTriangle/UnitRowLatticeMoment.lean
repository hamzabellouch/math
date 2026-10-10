import OAI.Geometry.HeilbronnTriangle.RowLatticeMoment
import OAI.Geometry.HeilbronnTriangle.PrimePowerData

namespace OAI


namespace Problem355.LatticeMoment

open RowPairingDivisor RowLattice

theorem matrix_pairing_divisor_moment_index_of_unit
    (S : Finset (Fin 3 → ℤ)) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (B k : ℕ) (R : ℝ) (hB : B.Prime) (hR : (B : ℝ) ^ k ≤ R)
    (hunit : IsUnit ((A 0 0 : ℤ) : ZMod (B ^ k)))
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)| ≤ R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1) :
    ∑ x ∈ S, (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 ≤
      128 * R ^ 3 *
        ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) := by
  let d : PrimePowerData B k (A.map fun z : ℤ => (z : ZMod (B ^ k))) :=
    PrimePowerData.ofUnit hB hunit
  have hdR : (B : ℝ) ^ d.e ≤ R := le_trans
    (by exact_mod_cast Nat.pow_le_pow_right hB.pos d.e_le_k) hR
  apply matrix_pairing_divisor_moment_index_real S A B d.b d.e k R hB hdR
    d.b_le_e d.e_le_k d.left d.right ?_ hbox hprimitive
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

theorem matrix_pairing_divisor_shell_moment_of_unit
    (S : Finset (Fin 3 → ℤ)) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (B k : ℕ) (R : ℝ) (hB : B.Prime) (hR : (B : ℝ) ^ k ≤ R)
    (hunit : IsUnit ((A 0 0 : ℤ) : ZMod (B ^ k)))
    (hnorm : ∀ x ∈ S,
      ‖(WithLp.toLp 2 (fun i => (x i : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 * R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1) :
    ∑ x ∈ S, (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 ≤
      1024 * R ^ 3 *
        ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) := by
  let d : PrimePowerData B k (A.map fun z : ℤ => (z : ZMod (B ^ k))) :=
    PrimePowerData.ofUnit hB hunit
  have hdR : (B : ℝ) ^ d.e ≤ R := le_trans
    (by exact_mod_cast Nat.pow_le_pow_right hB.pos d.e_le_k) hR
  apply matrix_pairing_divisor_shell_moment S A B d.b d.e k R hB hdR
    d.b_le_e d.e_le_k d.left d.right ?_ hnorm hprimitive
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

theorem matrix_pairing_divisor_cube_div_index_le_of_unit
    (A : Matrix (Fin 3) (Fin 3) ℤ) (x z : Fin 3 → ℤ)
    (B k : ℕ) (hB : B.Prime)
    (hunit : IsUnit ((A 0 0 : ℤ) : ZMod (B ^ k)))
    (hprimitive : dotProduct x z = 1) :
    (matrixPairingDivisor (B ^ k) A x : ℝ) ^ 3 /
      ((integerRowLattice (B ^ k) (A.map fun z : ℤ => (z : ZMod (B ^ k)))).index : ℝ) ≤
        ((B : ℝ) ^ k) ^ 2 := by
  let d : PrimePowerData B k (A.map fun z : ℤ => (z : ZMod (B ^ k))) :=
    PrimePowerData.ofUnit hB hunit
  apply matrix_pairing_divisor_cube_div_index_le A x z B d.b d.e k hB
    d.b_le_e d.e_le_k d.left d.right ?_ hprimitive
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

end Problem355.LatticeMoment

end OAI
