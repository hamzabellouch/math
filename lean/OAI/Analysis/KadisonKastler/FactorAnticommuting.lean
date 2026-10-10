import OAI.Analysis.KadisonKastler.MatrixUnitsExistence
import OAI.Analysis.KadisonKastler.JordanOrientation

namespace OAI

/-! # Anticommuting unitaries in finite factors

The two Pauli matrices in a unital system of two-by-two matrix units give
selfadjoint anticommuting unitaries. Every II₁ factor contains such a system,
so the quantitative Jordan orientation test applies without an additional
assumption on the source factor.
-/

namespace KadisonKastler

noncomputable section

section MatrixUnits

variable {A : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
  (E : Generator.MatrixUnitSystem (Fin 2) A)

/-- The diagonal Pauli matrix in the given matrix units. -/
def matrixUnitsPauliZ : A := E.entry 0 0 - E.entry 1 1

/-- The off-diagonal Pauli matrix in the given matrix units. -/
def matrixUnitsPauliX : A := E.entry 0 1 + E.entry 1 0

theorem matrixUnitsPauliZ_star : star (matrixUnitsPauliZ E) = matrixUnitsPauliZ E := by
  simp only [matrixUnitsPauliZ, star_sub, E.star_entry]

theorem matrixUnitsPauliX_star : star (matrixUnitsPauliX E) = matrixUnitsPauliX E := by
  simp only [matrixUnitsPauliX, star_add, E.star_entry, add_comm]

theorem matrixUnitsPauliZ_sq : matrixUnitsPauliZ E * matrixUnitsPauliZ E = 1 := by
  have ht : E.entry 0 0 + E.entry 1 1 = 1 := by
    simpa only [Fin.sum_univ_two] using E.total
  simpa [matrixUnitsPauliZ, sub_mul, mul_sub, E.mul_entry] using ht

theorem matrixUnitsPauliX_sq : matrixUnitsPauliX E * matrixUnitsPauliX E = 1 := by
  have ht : E.entry 0 0 + E.entry 1 1 = 1 := by
    simpa only [Fin.sum_univ_two] using E.total
  simpa [matrixUnitsPauliX, add_mul, mul_add, E.mul_entry, add_comm] using ht

/-- The diagonal Pauli unitary. -/
def matrixUnitsPauliZUnitary : unitary A :=
  ⟨matrixUnitsPauliZ E, by
    constructor <;> rw [matrixUnitsPauliZ_star, matrixUnitsPauliZ_sq]⟩

/-- The off-diagonal Pauli unitary. -/
def matrixUnitsPauliXUnitary : unitary A :=
  ⟨matrixUnitsPauliX E, by
    constructor <;> rw [matrixUnitsPauliX_star, matrixUnitsPauliX_sq]⟩

theorem matrixUnitsPauli_anticommute :
    (matrixUnitsPauliZUnitary E : A) * (matrixUnitsPauliXUnitary E : A) =
      -((matrixUnitsPauliXUnitary E : A) * (matrixUnitsPauliZUnitary E : A)) := by
  change matrixUnitsPauliZ E * matrixUnitsPauliX E =
    -(matrixUnitsPauliX E * matrixUnitsPauliZ E)
  simp [matrixUnitsPauliZ, matrixUnitsPauliX, add_mul, mul_add,
    E.mul_entry, sub_eq_add_neg, add_comm]

/-- A unital two-by-two matrix algebra supplies the exact pair used in the
Jordan orientation argument. -/
theorem exists_anticommuting_unitaries_of_matrixUnits
    (E : Generator.MatrixUnitSystem (Fin 2) A) :
    ∃ a b : unitary A, star (a : A) = (a : A) ∧ star (b : A) = (b : A) ∧
      (a : A) * (b : A) = -((b : A) * (a : A)) :=
  ⟨matrixUnitsPauliZUnitary E, matrixUnitsPauliXUnitary E,
    matrixUnitsPauliZ_star E, matrixUnitsPauliX_star E, matrixUnitsPauli_anticommute E⟩

end MatrixUnits

section Factor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Every concrete II₁ factor contains selfadjoint anticommuting unitaries. -/
theorem exists_anticommuting_unitaries_of_II1
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    ∃ a b : unitary (Algebra M),
      star (a : Algebra M) = (a : Algebra M) ∧
      star (b : Algebra M) = (b : Algebra M) ∧
      (a : Algebra M) * (b : Algebra M) = -((b : Algebra M) * (a : Algebra M)) := by
  obtain ⟨E⟩ := exists_matrixUnits_of_size hM 2 (by decide)
  exact exists_anticommuting_unitaries_of_matrixUnits E

/-- A sufficiently close surjective Jordan map out of a II₁ factor has the
multiplicative orientation; no contractivity hypothesis is needed. -/
theorem PreservesJordan.multiplicative_of_close_of_II1
    {B D : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    [NormedRing D] [NormedAlgebra ℂ D]
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (θ : Algebra M →ₗ[ℂ] B) (ι : Algebra M →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (hsmall : 3 * e + e ^ 2 < 2) :
    ∀ x y, θ (x * y) = θ x * θ y := by
  have hunit : (1 : Algebra M) ≠ 0 := by
    intro h
    exact hM.nonzero (congrArg Subtype.val h).symm
  let : Nontrivial (Algebra M) := nontrivial_of_ne _ _ hunit
  obtain ⟨a, b, _, _, hab⟩ := exists_anticommuting_unitaries_of_II1 hM
  exact PreservesJordan.multiplicative_of_close_of_anticommuting_unitaries_without_contractivity
    θ ι κ hθ hsurj hprime he hι hclose a b hab hsmall

end Factor

end

end KadisonKastler

end OAI
