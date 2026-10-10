import OAI.Analysis.KadisonKastler.MatrixOrbitPairings
import OAI.Analysis.KadisonKastler.VectorStateFourthMoment

namespace OAI

/-! # Finite laws of the actual matrix-orbit samples

This converts the complex four-variable matrix-average identities to
real moment identities for a single product-valued sample. It supplies
the diagonal and the two off-diagonal inputs to the independent-sample
fourth-moment estimate.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The actual finite sample space for one left and one right unitary. -/
abbrev MatrixOrbitIndex (d : ℕ) := SignedPermutation (Fin d) × SignedPermutation (Fin d)

/-- An operator sampled from the finite two-sided matrix orbit. -/
def matrixOrbitSample {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (x : H →L[ℂ] H) (g : MatrixOrbitIndex d) : H →L[ℂ] H :=
  unitaryDoubleOrbit x (matrixUnitSignedRepresentation E g.1)
    (matrixUnitSignedRepresentation E g.2)

private theorem complex_expect_eq_average {G : Type*} [Fintype G] (f : G → ℂ) :
    (𝔼 g, f g) = finiteAverage f := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [finiteAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem re_average {G : Type*} [Fintype G] (f : G → ℂ) :
    (finiteAverage f).re = 𝔼 g, (f g).re := by
  rw [← complex_expect_eq_average]
  exact map_expect (Complex.reLm.restrictScalars ℚ≥0) f Finset.univ

private theorem expect_prod {G K : Type*} [Fintype G] [Fintype K]
    (f : G × K → ℝ) : (𝔼 p, f p) = 𝔼 g, 𝔼 k, f (g, k) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset G) (Finset.univ : Finset K) f

private theorem state_conj (M : VonNeumannAlgebra H) (Ω : H)
    (v : unitary (H →L[ℂ] H)) (hv : (v : H →L[ℂ] H) ∈ M)
    (hc : ∀ z ∈ M, inner ℂ Ω (((v : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (v : H →L[ℂ] H)) Ω))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    realVectorState Ω (unitaryConj v a) = realVectorState Ω a := by
  have h := hc (a * star (v : H →L[ℂ] H))
    (M.mul_mem ha (M.toStarSubalgebra.star_mem' hv))
  apply congrArg Complex.re
  change inner ℂ Ω (((v : H →L[ℂ] H) * a * star (v : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (a Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem v.property, mul_one] using h

/-- The fourth moment of a single orbit sample is unchanged by its two
unitaries, since the right unitary belongs to the state's centralizer. -/
theorem matrixOrbit_diagonal_fourth
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (g : MatrixOrbitIndex d) :
    realVectorState Ω ((star (matrixOrbitSample E x g) * matrixOrbitSample E x g) ^ 2) =
      realVectorState Ω ((star x * x) ^ 2) := by
  change realVectorState Ω ((star (unitaryDoubleOrbit x _ _) *
    unitaryDoubleOrbit x _ _) ^ 2) = _
  rw [unitaryDoubleOrbit_star_mul_self]
  have he := (map_pow (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H)
    (matrixUnitSignedRepresentation E g.2)) (star x * x) 2).symm
  change (unitaryConj (matrixUnitSignedRepresentation E g.2) (star x * x)) ^ 2 =
    unitaryConj (matrixUnitSignedRepresentation E g.2) ((star x * x) ^ 2) at he
  rw [he]
  exact state_conj M Ω _ (hEM (matrixUnitSignedRepresentation_mem E g.2))
    (hc _ (matrixUnitSignedRepresentation_mem E g.2)) _
    (M.pow_mem (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx) 2)

/-- The first off-diagonal moment is the actual first independent-copy
matrix pairing, expressed as a real number. -/
theorem matrixOrbit_first_pairing_expect
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    (𝔼 g : MatrixOrbitIndex d, 𝔼 h : MatrixOrbitIndex d,
      realVectorState Ω ((star (matrixOrbitSample E x g) * matrixOrbitSample E x g) *
        (star (matrixOrbitSample E x h) * matrixOrbitSample E x h))) =
      realVectorState Ω ((star x * x) * matrixUnitAverage E (star x * x)) := by
  rw [expect_prod]
  simp_rw [expect_prod]
  change (𝔼 i, 𝔼 j, 𝔼 k, 𝔼 l,
    (operatorVectorState Ω
      ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
        (matrixUnitSignedRepresentation E j)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
          (matrixUnitSignedRepresentation E j)) *
       (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
        (matrixUnitSignedRepresentation E l)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
          (matrixUnitSignedRepresentation E l)))).re) = _
  simp_rw [← re_average]
  rw [matrixOrbit_first_pairing_average M Ω E hEM hc x hx]
  rfl

/-- The positive mixed pairing similarly becomes one averaged left
square between `x*` and `x`. -/
theorem matrixOrbit_third_pairing_expect
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    (𝔼 g : MatrixOrbitIndex d, 𝔼 h : MatrixOrbitIndex d,
      realVectorState Ω ((star (matrixOrbitSample E x g) * matrixOrbitSample E x h) *
        (star (matrixOrbitSample E x h) * matrixOrbitSample E x g))) =
      realVectorState Ω (star x * matrixUnitAverage E (x * star x) * x) := by
  rw [expect_prod]
  simp_rw [expect_prod]
  change (𝔼 i, 𝔼 j, 𝔼 k, 𝔼 l,
    (operatorVectorState Ω
      ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
        (matrixUnitSignedRepresentation E j)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
          (matrixUnitSignedRepresentation E l)) *
       (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
        (matrixUnitSignedRepresentation E l)) *
        unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
          (matrixUnitSignedRepresentation E j)))).re) = _
  simp_rw [← re_average]
  rw [matrixOrbit_third_pairing_average M Ω E hEM hc x hx]
  rfl

end

end KadisonKastler

end OAI
