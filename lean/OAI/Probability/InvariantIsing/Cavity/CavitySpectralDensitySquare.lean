import OAI.Probability.InvariantIsing.Cavity.CavityMatrixResolventBound

namespace OAI

/-! The derivative of the matrix resolvent is its square divided by
the scalar second resolvent. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavitySpectralMatrixDensity_eq_square {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixDensity ρ eig hρ hsum A hA x =
      (1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x)) •
        (cavitySpectralMatrixPath ρ eig hρ hsum A hA x *
          cavitySpectralMatrixPath ρ eig hρ hsum A hA x) := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  change U (Matrix.diagonal _) = _ • (U (Matrix.diagonal _) * U (Matrix.diagonal _))
  rw [← map_mul, Matrix.diagonal_mul_diagonal, ← map_smul, ← Matrix.diagonal_smul]
  apply congrArg U
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.smul_apply, smul_eq_mul,
    cavityScalarResolvent_pos_eq ρ eig hρ hsum a (heig i) hx,
    one_div, pow_two, mul_inv]

end InvariantIsing

end

end OAI
