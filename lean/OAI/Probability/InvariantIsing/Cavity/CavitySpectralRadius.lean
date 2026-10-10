import OAI.Probability.InvariantIsing.Cavity.CavityFullGibbsMoment

namespace OAI

/-! Uniform radius-cutoff removal for bounded tests of the full spectral
cavity Gibbs law, including its zero-normalizer convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_spectral_radius_error {ι : Type*} [Fintype ι] {d k n : ℕ}
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
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (r : ℕ)
    (F : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      (Fin r → ((EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k)) → ℝ)
    (hF : Measurable F) {rad B : ℝ} (hrad : 0 < rad) (hB : 0 ≤ B)
    (hFb : ∀ ω σ, |F (ω, σ)| ≤ B) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let ν := cavityRootedFullGibbs n K (H n) L C π
    |∫ ω, cavityWeightedReplicaMean (ν ω)
      (fun z => cavityRadialCutoff rad ‖cavityRootedField n z.1‖) (fun σ => F (ω, σ)) -
        ∫ σ, F (ω, σ) ∂Measure.pi (fun _ : Fin r => ν ω) ∂P| ≤
      2 * B * r * cavityGaussianLinearMomentBound d 2
        (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ / rad^2 := by
  intro K H S₀ P ν
  have hm := cavity_rooted_spectral_gibbs_moment ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
    q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C 2
  exact cavity_soft_radius_mean_error P ν ν.measurable
    (fun z => cavityRootedField n z.2.1)
    ((measurable_cavityRootedField n).comp measurable_snd.fst)
    F hF hm.1 hm.2.1 hrad hB hFb hm.2.2

end InvariantIsing

end

end OAI
