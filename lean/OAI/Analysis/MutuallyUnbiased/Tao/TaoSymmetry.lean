import OAI.Analysis.MutuallyUnbiased.Matrix.Definitions
import OAI.LinearAlgebra.Hadamard.TaoFourier

namespace OAI

/-! The cubic symmetry lemma for Tao's matrix and its normalized characters.

The natural exponents of `MUB6.tao` and the signed five-cycle exponents of
`HadamardSix.taoMatrix` agree modulo three. This identifies their characters
and transfers the row symmetry and signed charge invariance. -/

namespace MUB6

/-- The two five-cycle exponent conventions define the same complex matrix. -/
theorem tao_eq_hadamardSix : tao = HadamardSix.taoMatrix := by
  funext i j
  change HadamardSix.omega ^ taoExponent i j =
    HadamardSix.omega ^ HadamardSix.taoExponent i j
  rw [← zpow_natCast]
  apply HadamardSix.CubicSymmetry.omega_zpow_eq_of_zmod_eq
  fin_cases i <;> fin_cases j <;> decide

namespace CubicSymmetry

/-- Every row permutation of Tao's matrix extends by column permutations,
unit phases, and optional complex conjugation. -/
theorem every_row_permutation_complex (p : Equiv.Perm Coord) :
    ∃ (q : Equiv.Perm Coord) (conjugate : Bool) (U V : Coord → ℂ),
      (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
      ∀ i j, tao (p i) (q j) =
        U i * V j * (if conjugate then star (tao i j) else tao i j) := by
  rw [tao_eq_hadamardSix]
  exact HadamardSix.CubicSymmetry.every_row_permutation_complex p

/-- On balanced charges the Fourier norm is invariant under signed permutations. -/
theorem norm_g_signed_permute (a : Charge) (ha : Balanced a)
    (p : Equiv.Perm Coord) (negate : Bool) :
    ‖g tao (if negate then -(permuteCharge p a) else permuteCharge p a)‖ =
      ‖g tao a‖ := by
  change ‖HadamardSix.g tao
    (if negate then -(HadamardSix.permuteCharge p a)
     else HadamardSix.permuteCharge p a)‖ = ‖HadamardSix.g tao a‖
  rw [tao_eq_hadamardSix]
  exact HadamardSix.CubicSymmetry.norm_g_signed_permute a ha p negate

/-- The cubic symmetry lemma: matrix symmetries and invariance of Fourier norms
on the signed permutation orbits of balanced charges. -/
theorem cubic_symmetry :
    (∀ p : Equiv.Perm Coord,
      ∃ (q : Equiv.Perm Coord) (conjugate : Bool) (U V : Coord → ℂ),
        (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
        ∀ i j, tao (p i) (q j) =
          U i * V j * (if conjugate then star (tao i j) else tao i j)) ∧
    (∀ a : Charge, Balanced a → ∀ (p : Equiv.Perm Coord) (negate : Bool),
      ‖g tao (if negate then -(permuteCharge p a) else permuteCharge p a)‖ =
        ‖g tao a‖) :=
  ⟨every_row_permutation_complex, norm_g_signed_permute⟩

end CubicSymmetry
end MUB6

end OAI
