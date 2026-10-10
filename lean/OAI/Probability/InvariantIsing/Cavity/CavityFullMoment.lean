import OAI.Probability.InvariantIsing.Cavity.CavitySpectralMoment
import OAI.Probability.InvariantIsing.Cavity.CavityFullTilt

namespace OAI

/-! Uniform polynomial moments under the original full cavity factor.
The quadratic transformation is used only in the proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_rooted_spectral_full_moment {ι : Type*} [Fintype ι] {d k n : ℕ}
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
    let κ := cavityRootedPriorKernel n (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S₀ P κ ν V
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
  have hZ : ∀ᵐ ω ∂P, cavityResidualPartition n K (H n) ω.1 ω.2 < ∞ := by
    have hm := measurable_cavityResidualPartition n K H b
      (Matrix.isHermitian_iff_isSymm.mpr hK) hR hQR
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hm measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      (cavity_residual_partition_pos_finite n K H S b hbCascade hK hH hS hb hdet hΔ hQ
        hR hQR s).mono (fun _ h => h.2))
  have hlin := cavity_rooted_spectral_linear_moment ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
    q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C p
  let νlin := cavityRootedResidualKernel n K (H n) ×ₖ Kernel.const _ π
  let Vlin : (EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) × Spin k → ℝ :=
    fun z => cavityLogFactor 0 L C (cavityRootedField n z.1) z.2
  have he : ∀ᵐ ω ∂P, (νlin ω).tilted Vlin = (ν ω).tilted V := by
    filter_upwards [hZ] with ω hω
    simpa only [νlin, ν, κ, Kernel.prod_apply, Kernel.const_apply, Vlin, V] using
      cavity_rooted_full_tilt_eq n K (H n) L C π ω hω
  have hmean : (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) =ᵐ[P]
      (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(νlin ω).tilted Vlin) :=
    he.mono (fun _ h => by dsimp only; rw [h])
  refine ⟨?_, hlin.2.1.congr hmean.symm, ?_⟩
  · filter_upwards [hZ, hlin.1, he] with ω hω hωlin hωeq
    refine ⟨?_, ?_⟩
    · simpa only [ν, κ, Kernel.prod_apply, Kernel.const_apply, V] using
        cavity_rooted_full_exp_integrable n K (H n) L C π ω hω
          (by simpa only [Kernel.prod_apply, Kernel.const_apply] using hωlin.1)
    · rw [← hωeq]
      exact hωlin.2
  · rw [integral_congr_ae hmean]
    exact hlin.2.2

end InvariantIsing

end

end OAI
