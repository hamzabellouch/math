import OAI.Probability.InvariantIsing.Cavity.CavityFiniteMeasurableAverage
import OAI.Probability.InvariantIsing.Cavity.CavitySelectedRestrictedAverage

namespace OAI

/-! The capped Gaussian-marked spectral cascade numerator is exactly
the numerator of the actual finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_cascade_restricted_spin_average {m d n r k qdim : ℕ}
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
      ∫ T, ∫ z, ∫ σ : Fin r → LabeledLeaf n,
        cavityRestrictedFlatSpinValue K L C τ Bcut π
          (fun ε => F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ, ε))
          (cavityReplicaField n T σ z)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  have hav := cavity_finite_gaussian_measurable_average rho lam hrho hsum p q hq.monotone
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1 htop.le b
    (cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F)
    (measurable_cavityRestrictedSpinReplicaValue K L C τ hBcut (cavitySelectedGroupProjection e) π F)
    (cavityRestrictedSpinReplicaValue_bound K L C τ hBcut (cavitySelectedGroupProjection e) π F)
  change (∫ x, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) = _ at hav
  rw [hav]
  exact integral_congr_ae (ae_of_all _ fun T =>
    (cavity_selected_restricted_spin_average rho lam hrho hsum g e he heg p cut hcut hfirst hlast
      q hq hp htop T (Measure.pi (fun _ : Fin r => labeledLeafLaw n T)) K L C τ hBcut π F).symm)

end InvariantIsing

end

end OAI
