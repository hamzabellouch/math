import OAI.Probability.InvariantIsing.Cavity.CavityFullMoment
import OAI.Probability.InvariantIsing.Cavity.CavityTiltedCap

namespace OAI

/-! Uniform removal of the logarithmic cap for the full spectral cavity factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_spectral_cap_error {ι : Type*} [Fintype ι] {d k n : ℕ}
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
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) {T : ℝ} (hT : 0 < T) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let κ := cavityRootedPriorKernel n (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    0 ≤ (∫ ω, Real.log (∫ z, Real.exp (V z) ∂ν ω) -
      Real.log (∫ z, Real.exp (min (V z) T) ∂ν ω) ∂P) ∧
    (∫ ω, Real.log (∫ z, Real.exp (V z) ∂ν ω) -
      Real.log (∫ z, Real.exp (min (V z) T) ∂ν ω) ∂P) ≤
      2 * (cavityMatrixMass K + cavityMatrixMass L + cavityMatrixMass C)^2 *
        (1 + cavityGaussianLinearMomentBound d 4 (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹) / T := by
  intro K H S₀ P κ ν V
  have hm := cavity_rooted_spectral_full_moment ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
    q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C 4
  exact cavity_quadratic_cap_mean_error P ν ν.measurable (fun z => V z.2)
    (fun z => ‖cavityRootedField n z.1‖)
    ((measurable_cavityRootedLogFactor n K L C).comp measurable_snd)
    (hm.1.mono (fun _ h => h.1)) (hm.1.mono (fun _ h => h.2)) hm.2.1
    (add_nonneg (add_nonneg (cavityMatrixMass_nonneg K) (cavityMatrixMass_nonneg L))
      (cavityMatrixMass_nonneg C)) hT
    (fun _ z => cavity_logFactor_growth K L C (cavityRootedField n z.1) z.2) hm.2.2

end InvariantIsing

end

end OAI
