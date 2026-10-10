import OAI.Probability.InvariantIsing.Cavity.CavityFullMoment
import OAI.Probability.InvariantIsing.Cavity.CavityDiagonalSpectralPrecision

namespace OAI

/-! Full original-prior cavity moments with the precision conditions
proved for the actual diagonal base spectrum. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_spectral_upper_posSemidef {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (M : ℝ)
    (hM : ∀ i, hA.eigenvalues i ≤ M) :
    (M • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  have hu : U (Matrix.diagonal hA.eigenvalues) = A := by
    simpa [U] using hA.spectral_theorem.symm
  have hc : Matrix.diagonal (fun _ : Fin d => M) = M • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have he : U (Matrix.diagonal (fun i => M - hA.eigenvalues i)) = M • 1 - A := by
    rw [show Matrix.diagonal (fun i => M - hA.eigenvalues i) =
      Matrix.diagonal (fun _ => M) - Matrix.diagonal hA.eigenvalues by
        simp only [← Matrix.diagonal_sub],
      map_sub, hc, map_smul, map_one, hu]
  have hp := (Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hM i))).mul_mul_conjTranspose_same
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  rw [← he]
  simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hp

theorem cavity_diagonal_spectral_full_moment {ι : Type*} [Fintype ι] {d k n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (e : Fin d → ℝ) (hdiag : A₀ = Matrix.diagonal e)
    (a : ι) (hemax : ∀ i, e i ≤ eig a) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 < x i) (hxmono : Antitone x)
    (hbCascade : CascadeExponents n b) (hb : ∀ i, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hS : ∀ i, (S i).PosSemidef)
    (hΔ : ∀ i,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let κ := cavityRootedPriorKernel n (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  subst A₀
  have hK : (A - Matrix.diagonal e).transpose = A - Matrix.diagonal e := by
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hu := cavity_spectral_upper_posSemidef A hA (eig a) heig
  have hQ (i : ℕ) : (cavityFactorPrecision
      (b i • cavityBackwardQuadratic (A - Matrix.diagonal e)
        (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) hA₀ (x (i + 1))))
      (CFC.sqrt (S i))).PosDef :=
    cavity_diagonal_spectral_step_precision ρ eig hρ hsum A e hA₀ a heig₀ hemax hK hu
      (hx (i + 1)) (hxmono (Nat.le_succ i)) (hb i).le (S i) (hS i) (hΔ i)
  have hH := cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e hA₀ a heig₀ hemax (hx n)
  have hR : (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) hA₀ (x n)).PosSemidef := by
    rw [hH]
    exact Matrix.PosSemidef.diagonal (fun i => (inv_pos.mpr
      (sub_pos.mpr ((hemax i).trans_lt ((finiteInverse_spec ρ eig hρ hsum (hx n)).1 a)))).le)
  have hQR := cavity_diagonal_spectral_terminal_precision ρ eig hρ hsum A e hA₀ a heig₀ hemax hK hu (hx n)
  exact cavity_rooted_spectral_full_moment ρ eig hρ hsum A (Matrix.diagonal e) hA hA₀
    a heig heig₀ q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C p

end InvariantIsing

end

end OAI
