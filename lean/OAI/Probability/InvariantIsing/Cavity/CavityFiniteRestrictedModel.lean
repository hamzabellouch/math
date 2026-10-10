import OAI.Probability.InvariantIsing.Cavity.CavityFiniteRestrictedNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledRestrictedModel

namespace OAI

/-! The spectral Gaussian numerator in the measurable finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_model_numerator {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (b : ℕ → ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ ω, cavityLabeledRestrictedNumerator n K
        (cavityFiniteCovariancePath rho lam hrho hsum g p q n) L C π τ Bcut
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q) F ω
        ∂cavityLabeledDisorderLaw n b
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)
          (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q) := by
  intro B
  rw [integral_cavityLabeledRestrictedNumerator]
  exact cavity_finite_restricted_numerator rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop b K L C τ hBcut π F

end InvariantIsing

end

end OAI
