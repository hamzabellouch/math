import OAI.Geometry.EinsteinFour.FiniteRadialComparison
import OAI.Geometry.EinsteinFour.ScalarNormalizer
import OAI.Geometry.EinsteinFour.SineModeLimit

namespace OAI

/-! Applying the finite comparison to the actual scalar Dirichlet reference. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def referenceMatrix (t : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  scalarDirichlet N (2 - (t / (N + 1)) ^ 2)

def curvatureDirichlet {N : ℕ} (t : ℝ) (A : Fin N → NormalMatrix) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  scalarLift (referenceMatrix t N) - (t / (N + 1)) ^ 2 • Matrix.blockDiagonal A

/-- The scalar normalizer and its sine eigenmode are fully instantiated.
Only positivity of the actual curvature Dirichlet matrix remains here. -/
theorem reference_determinant_comparison {N : ℕ} (hN : 0 < N) (t : ℝ)
    (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0)
    (hfirst : 0 < firstEigenvalue t N) (hK : (curvatureDirichlet t A).PosDef) :
    (curvatureDirichlet t A).det / (referenceMatrix t N).det ^ 3 ≤
      ((1 : NormalMatrix) - ((t / (N + 1)) ^ 2 / firstEigenvalue t N) •
        (∑ i, unitFirstSineVector N i ^ 2 • A i)).det := by
  let L := referenceMatrix t N
  let G := scalarNormalizer L
  let w := unitFirstSineVector N
  let a := t / (N + 1)
  let g := 1 / Real.sqrt (firstEigenvalue t N)
  have hL : L.PosDef := scalarDirichlet_posDef N _ hfirst
  have hn : G * L * G = 1 := scalarNormalizer_normalizes hL
  have hsym : Gᵀ = G := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef L).isHermitian.eq
  have hlift : (scalarLift G)ᴴ = scalarLift G := by
    ext ⟨u, i⟩ ⟨v, j⟩
    change (1 : NormalMatrix) v u * G j i = (1 : NormalMatrix) u v * G i j
    rw [show G j i = G i j from congrFun (congrFun hsym i) j]
    simp only [Matrix.one_apply, eq_comm]
  have hunit : IsUnit (scalarLift G) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_scalarLift]
    exact (Matrix.isUnit_det_of_left_inverse hn).pow 3
  have hpos : (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) *
      scalarLift G).PosDef := by
    have hp := hK.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
    simpa only [hlift, curvatureDirichlet, L, a] using hp
  have heigen : G *ᵥ w = g • w :=
    scalarNormalizer_eigenvector hL hfirst (unitFirstSineVector_eigenvector N _)
  have hb := finite_normalized_radial_comparison hN G L A w a g
    (unitFirstSineVector_norm hN) hsym hn heigen hA hpos
  rw [det_normalized_matrix G L _ hn] at hb
  have hcoef : (a * g) ^ 2 = a ^ 2 / firstEigenvalue t N := by
    dsimp [g]
    simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt hfirst.le]
    ring
  rw [hcoef] at hb
  exact hb

end

end PositiveEinsteinFour.Jacobi

end OAI
