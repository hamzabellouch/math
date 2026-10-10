import OAI.Analysis.KadisonKastler.MatrixStateMoments

namespace OAI

/-! # Fourth-moment pairings of actual two-sided matrix orbits

The sampled elements are `u*x*v*`. Their first and third sign-pairing
terms reduce exactly to the independent matrix averages in
`MatrixStateMoments`; the reductions use the vector-state centralizer,
not a trace identity for arbitrary elements.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- One actual sample of the two-sided unitary orbit. -/
def unitaryDoubleOrbit (x : H →L[ℂ] H)
    (u v : unitary (H →L[ℂ] H)) : H →L[ℂ] H :=
  (u : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)

/-- The left orbit unitary cancels from the right square. -/
theorem unitaryDoubleOrbit_star_mul_self (x : H →L[ℂ] H)
    (u v : unitary (H →L[ℂ] H)) :
    star (unitaryDoubleOrbit x u v) * unitaryDoubleOrbit x u v =
      unitaryConj v (star x * x) := by
  simp only [unitaryDoubleOrbit, star_mul, star_star, unitaryConj]
  calc
    _ = (v : H →L[ℂ] H) * star x *
        (star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) * x * star (v : H →L[ℂ] H) := by
      noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem u.property]; noncomm_ring

/-- The mixed positive square exposes the relative left conjugation. -/
theorem unitaryDoubleOrbit_mixed_square (x : H →L[ℂ] H)
    (u v u' v' : unitary (H →L[ℂ] H)) :
    (star (unitaryDoubleOrbit x u v) * unitaryDoubleOrbit x u' v') *
        (star (unitaryDoubleOrbit x u' v') * unitaryDoubleOrbit x u v) =
      unitaryConj v (star x * unitaryConj (star u)
        (unitaryConj u' (x * star x)) * x) := by
  simp only [unitaryDoubleOrbit, unitaryConj, star_mul, star_star, Unitary.coe_star]
  calc
    _ = (v : H →L[ℂ] H) * star x * star (u : H →L[ℂ] H) *
        (u' : H →L[ℂ] H) * x *
        (star (v' : H →L[ℂ] H) * (v' : H →L[ℂ] H)) *
        star x * star (u' : H →L[ℂ] H) * (u : H →L[ℂ] H) *
        x * star (v : H →L[ℂ] H) := by noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem v'.property]; noncomm_ring

private theorem state_conjugation (M : VonNeumannAlgebra H) (Ω : H)
    (v : unitary (H →L[ℂ] H)) (hv : (v : H →L[ℂ] H) ∈ M)
    (hc : ∀ z ∈ M, inner ℂ Ω (((v : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (v : H →L[ℂ] H)) Ω))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    operatorVectorState Ω (unitaryConj v a) = operatorVectorState Ω a := by
  have h := hc (a * star (v : H →L[ℂ] H))
    (M.mul_mem ha (M.toStarSubalgebra.star_mem' hv))
  change inner ℂ Ω (((v : H →L[ℂ] H) * a * star (v : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (a Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem v.property, mul_one] using h

/-- Removing the right conjugation from the vector state identifies the
third pairing for two actual orbit samples. -/
theorem vectorState_unitaryDoubleOrbit_mixed_square
    (M : VonNeumannAlgebra H) (Ω : H) (x : H →L[ℂ] H) (hx : x ∈ M)
    (u v u' v' : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) (hv : (v : H →L[ℂ] H) ∈ M)
    (hu' : (u' : H →L[ℂ] H) ∈ M)
    (hc : ∀ z ∈ M, inner ℂ Ω (((v : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (v : H →L[ℂ] H)) Ω)) :
    operatorVectorState Ω
      ((star (unitaryDoubleOrbit x u v) * unitaryDoubleOrbit x u' v') *
        (star (unitaryDoubleOrbit x u' v') * unitaryDoubleOrbit x u v)) =
      operatorVectorState Ω (star x * unitaryConj (star u)
        (unitaryConj u' (x * star x)) * x) := by
  rw [unitaryDoubleOrbit_mixed_square]
  apply state_conjugation M Ω v hv hc
  have hsx := M.toStarSubalgebra.star_mem' hx
  have hsu := M.toStarSubalgebra.star_mem' hu
  have hsu' := M.toStarSubalgebra.star_mem' hu'
  simp only [unitaryConj, Unitary.coe_star, star_star]
  change star x * ((star (u : H →L[ℂ] H)) *
    ((u' : H →L[ℂ] H) * (x * star x) * star (u' : H →L[ℂ] H)) *
      (u : H →L[ℂ] H)) * x ∈ M
  exact M.mul_mem (M.mul_mem hsx
    (M.mul_mem (M.mul_mem hsu
      (M.mul_mem (M.mul_mem hu' (M.mul_mem hx hsx)) hsu')) hu)) hx

/-- Averaging the first pairing over the four independent matrix samples
is precisely the first scalar expression of `MatrixStateMoments`. -/
theorem matrixOrbit_first_pairing_average
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    finiteAverage (fun i : SignedPermutation (Fin d) =>
      finiteAverage (fun j : SignedPermutation (Fin d) =>
        finiteAverage (fun k : SignedPermutation (Fin d) =>
          finiteAverage (fun l : SignedPermutation (Fin d) =>
            operatorVectorState Ω
              ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                (matrixUnitSignedRepresentation E j)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                  (matrixUnitSignedRepresentation E j)) *
               (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                (matrixUnitSignedRepresentation E l)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                  (matrixUnitSignedRepresentation E l))))))) =
      operatorVectorState Ω ((star x * x) * matrixUnitAverage E (star x * x)) := by
  simp only [unitaryDoubleOrbit_star_mul_self, finiteAverage_const]
  exact matrixState_two_orbit_average M Ω E hEM hc (star x * x) (star x * x)
    (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx)
    (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx)

/-- Averaging the third pairing over four independent matrix samples
reduces to the relative left-unitary average sandwiched by `x*` and `x`. -/
theorem matrixOrbit_third_pairing_average
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    finiteAverage (fun i : SignedPermutation (Fin d) =>
      finiteAverage (fun j : SignedPermutation (Fin d) =>
        finiteAverage (fun k : SignedPermutation (Fin d) =>
          finiteAverage (fun l : SignedPermutation (Fin d) =>
            operatorVectorState Ω
              ((star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                (matrixUnitSignedRepresentation E j)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                  (matrixUnitSignedRepresentation E l)) *
               (star (unitaryDoubleOrbit x (matrixUnitSignedRepresentation E k)
                (matrixUnitSignedRepresentation E l)) *
                unitaryDoubleOrbit x (matrixUnitSignedRepresentation E i)
                  (matrixUnitSignedRepresentation E j))))))) =
      operatorVectorState Ω (star x * matrixUnitAverage E (x * star x) * x) := by
  have he (i j k l : SignedPermutation (Fin d)) :=
    vectorState_unitaryDoubleOrbit_mixed_square M Ω x hx
      (matrixUnitSignedRepresentation E i) (matrixUnitSignedRepresentation E j)
      (matrixUnitSignedRepresentation E k) (matrixUnitSignedRepresentation E l)
      (hEM (matrixUnitSignedRepresentation_mem E i))
      (hEM (matrixUnitSignedRepresentation_mem E j))
      (hEM (matrixUnitSignedRepresentation_mem E k))
      (hc _ (matrixUnitSignedRepresentation_mem E j))
  simp only [he, finiteAverage_const]
  exact matrixState_relative_orbit_average Ω E (star x) (x * star x) x

end

end KadisonKastler

end OAI
