import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCascadeSpinAverage
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianCappedNumerator

namespace OAI

/-! Exact identification of the capped spectral-block spin observable
with the ordinary finite cavity replica numerator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_capped_numerator {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (b : ℕ → ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ sg, cavityWeightNumerator
        (((labeledLeafLaw n T).prod (multivariateGaussian 0
          (cavityFiniteCovariancePath rho lam hrho hsum g p q n))).prod π)
        (fun v => Real.exp (min (cavityLogFactor K L C
          (cavityLeafSum n sg.1
            (labeledNoiseLeaf _ n (T, markForestOfCoords _ n sg.2) v.1.1) + v.1.2) v.2) τ))
        (fun ξ => F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q
          (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  rw [cavity_finite_cascade_spin_average rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop b K L C τ π F]
  exact integral_congr_ae (ae_of_all _ fun T => cavity_gaussian_capped_numerator T
    (labeledLeafLaw n T) _ _ _ K L C τ π
    (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q) F)

end InvariantIsing

end

end OAI
