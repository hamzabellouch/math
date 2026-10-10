import OAI.Probability.InvariantIsing.Cavity.CavitySpectralCovariance
import OAI.Probability.InvariantIsing.Cavity.CavitySpinLinearMoment

namespace OAI

/-! Uniform radial moments for the actual spectral quadratic cavity law,
after its remaining spin-linear tilt. No Gaussian marginal or norm bound
is assumed: both are derived from the spectral data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_spectral_linear_moment {ι : Type*} [Fintype ι] {d k n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 < x i)
    (hbCascade : CascadeExponents n b) (hb : ∀ i, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hS : ∀ i, (S i).PosSemidef)
    (hΔ : ∀ i,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic (A - A₀)
        (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1))))
      (CFC.sqrt (S i))).PosDef)
    (hR : (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x n)).PosSemidef)
    (hQR : (cavityFactorPrecision (A - A₀)
      (CFC.sqrt (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x n)))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let κ := cavityRootedResidualKernel n K (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor 0 L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S₀ P κ ν V
  let J := fun i => (1 - H i * K)⁻¹
  let Sfull := J 0 * S₀ * (J 0).transpose +
    ((∑ i : Fin n, J i * S i * (J (i + 1)).transpose) + cavityResolvent K (H n))
  have hS₀ : S₀.PosSemidef :=
    (cavitySpectralMatrixDensity_posSemidef ρ eig hρ hsum A₀ hA₀ a heig₀ (hx 0)).smul hq0
  have hK : K.transpose = K := by
    dsimp only [K]
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH (i : ℕ) : (H i).transpose = H i := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i),
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i)
  have hSfull : Sfull.PosSemidef := by
    apply Matrix.PosSemidef.add
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hS₀.mul_mul_conjTranspose_same (J 0)
    · exact (Matrix.posSemidef_sum Finset.univ (fun (i : Fin n) _ =>
        cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
          (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i))).add
            (cavity_tilt_covariance_posSemidef K (H n) hR hQR)
  have hnorm : ‖Sfull‖ ≤ (ρ a)⁻¹ :=
    cavity_spectral_total_covariance_bound ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
      q x b S hq hq0 (fun i _ => hx i) (fun i _ => hb i) hgap hlast (fun i _ => hΔ i)
  have hlaw : (κ ∘ₘ P).map (cavityRootedField n) = multivariateGaussian 0 Sfull :=
    cavity_rooted_quadratic_gaussian n K H S b S₀ hS₀ hbCascade hK hH hS hb hdet hΔ hQ hR hQR
  exact cavity_spin_linear_tilt_gaussian_moment P κ (cavityRootedField n)
    (measurable_cavityRootedField n) π Sfull hSfull hlaw L C hnorm p

end InvariantIsing

end

end OAI
