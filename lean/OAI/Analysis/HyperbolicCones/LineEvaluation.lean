import OAI.Analysis.HyperbolicCones.PolynomialEvaluation

namespace OAI

noncomputable section

open Matrix Polynomial MvPolynomial
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem polynomial_eval₂ {K : Type u} [CommRing K] (f : ℝ →+* K) (v : Coord → K) :
    MvPolynomial.eval₂ f v polynomial = matrixValue
      (symmetricCoordinates fun ij => v (Sum.inl (Sum.inl ij)))
      (symmetricCoordinates fun ij => v (Sum.inl (Sum.inr ij)))
      (fun i => v (Sum.inr i)) := by
  change (MvPolynomial.eval₂Hom f v) (matrixValue _ _ _) = _
  rw [matrixValue_map, symmetricCoordinates_map, symmetricCoordinates_map]
  simp

theorem symmetricCoordinates_affine {K : Type u} [CommRing K]
    (f : ℝ →+* K) (X : Sym 4) (t : K) :
    symmetricCoordinates (fun ij => f ((1 : Mat 4 ℝ) ij.val.1 ij.val.2) * t -
      f ((X : Mat 4 ℝ) ij.val.1 ij.val.2)) =
        t • (1 : Mat 4 K) - (X : Mat 4 ℝ).map f := by
  classical
  ext i j
  have hX : (X : Mat 4 ℝ).IsHermitian := X.property
  have hsym : (X : Mat 4 ℝ) j i = (X : Mat 4 ℝ) i j := by
    simpa using hX.apply i j
  by_cases h : i ≤ j
  · simp [symmetricCoordinates, h, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      mul_comm]
  · simp [symmetricCoordinates, h, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      eq_comm, hsym, mul_comm]

theorem linePolynomial_eval₂ {K : Type u} [CommRing K]
    (f : ℝ →+* K) (X Z : Sym 4) (y : Fin 3 → ℝ) (t : K) :
    (linePolynomial ((X, Z), y)).eval₂ f t = matrixValue
      (t • (1 : Mat 4 K) - (X : Mat 4 ℝ).map f)
      (t • (1 : Mat 4 K) - (Z : Mat 4 ℝ).map f)
      (fun i => -f (y i)) := by
  let g := Polynomial.eval₂RingHom f t
  have hg : g.comp Polynomial.C = f := by
    ext a
    simp [g]
  change g ((MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates ((X, Z), y) i))) polynomial) = _
  rw [MvPolynomial.map_eval₂Hom, hg]
  change MvPolynomial.eval₂ f _ polynomial = _
  rw [polynomial_eval₂]
  simp only [g, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change matrixValue
    (symmetricCoordinates (fun ij => f ((1 : Mat 4 ℝ) ij.val.1 ij.val.2) * t -
      f ((X : Mat 4 ℝ) ij.val.1 ij.val.2)))
    (symmetricCoordinates (fun ij => f ((1 : Mat 4 ℝ) ij.val.1 ij.val.2) * t -
      f ((Z : Mat 4 ℝ) ij.val.1 ij.val.2)))
    (fun i => f 0 * t - f (y i)) = _
  rw [symmetricCoordinates_affine, symmetricCoordinates_affine]
  simp

end Paper256

end

end OAI
