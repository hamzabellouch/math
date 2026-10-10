import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCascadeBlock

namespace OAI

/-! Gaussian marking commutes with the finite labeled-cascade
representation, including singular covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_cascade_gaussian_average {m n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n, ∫ z,
        F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho
          (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  obtain ⟨G, hG⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance k rho x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance k rho)⟩
  have hS : ∀ᵐ x ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray),
      (cavityGroupBlockCovariance k rho (B x)).PosSemidef := by
    apply cavity_cascade_group_covariance_posSemidef n b _
      (hq.comp (cavityFiniteLevel_monotone n))
      (by simpa only [Function.comp_apply, cavityFiniteLevel_zero] using hq0)
      (by simpa only [Function.comp_apply, cavityFiniteLevel_last] using hq1)
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p)
      (continuous_cavityCanonicalLabel rho lam hrho hsum p)
      (cavityCanonicalCoordinate_monotone rho lam hrho hsum p)
      (fun a => cavityCanonicalCoordinate_nonneg rho lam hrho hsum p a _)
      (fun a => cavityCanonicalCoordinate_le_diagonal rho lam hrho hsum p a _)
      rho (fun a => (hrho a).le)
  calc
    _ = ∫ x, H (B x)
        ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray) :=
      integral_congr_ae (hS.mono fun x hx => (hG _ _ hx).symm)
    _ = ∫ T, ∫ σ : Fin r → LabeledLeaf n,
        H (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) :=
      cavity_finite_cascade_block_average rho lam hrho hsum p q hq hq0 hq1 b H
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun σ =>
        hG _ _ (cavity_finite_group_covariance_posSemidef rho lam hrho hsum p q hq σ))

end InvariantIsing

end

end OAI
