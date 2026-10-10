import OAI.Probability.InvariantIsing.Cavity.CavityFullGibbs

namespace OAI

/-! The uniform moment bound expressed in the total full Gibbs kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_spectral_gibbs_moment {ι : Type*} [Fintype ι] {d k n : ℕ}
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
    let ν := cavityRootedFullGibbs n K (H n) L C π
    (∀ᵐ ω ∂P, Integrable (fun z => ‖cavityRootedField n z.1‖^p) (ν ω)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂ν ω) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂ν ω ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S₀ P ν
  have hm := cavity_rooted_spectral_full_moment ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
    q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C p
  let κ := cavityRootedPriorKernel n (H n) ×ₖ Kernel.const _ π
  let V : (EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) × Spin k → ℝ :=
    fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
  have he : ∀ᵐ ω ∂P, ν ω = (κ ω).tilted V := by
    filter_upwards [hm.1] with ω hω
    simpa only [κ, Kernel.prod_apply, Kernel.const_apply, V] using
      cavityRootedFullGibbs_eq_tilted n K (H n) L C π ω
        (by simpa only [Kernel.prod_apply, Kernel.const_apply] using hω.1)
  have hmean : (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂ν ω) =ᵐ[P]
      (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(κ ω).tilted V) :=
    he.mono (fun _ h => by dsimp only; rw [h])
  refine ⟨?_, hm.2.1.congr hmean.symm, ?_⟩
  · filter_upwards [he, hm.1] with ω hω hωm
    rw [hω]
    exact hωm.2
  · rw [integral_congr_ae hmean]
    exact hm.2.2

end InvariantIsing

end

end OAI
