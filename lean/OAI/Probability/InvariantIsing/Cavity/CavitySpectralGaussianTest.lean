import OAI.Probability.InvariantIsing.Cavity.CavityGaussianJointTest
import OAI.Probability.InvariantIsing.Spectral.SpectralArrayGeometry

namespace OAI

/-! The Gaussian marking limit keeps every overlap label in the finite
spectral block, rather than retaining only an averaged covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_gaussian_test_tendsto {m r : ℕ}
    {a : Type*} [Fintype a] [DecidableEq a]
    (P : ℕ → ProbabilityMeasure (SpectralArray m))
    (P₀ : ProbabilityMeasure (SpectralArray m)) (hP : Tendsto P atTop (𝓝 P₀))
    (C : SpectralBlock m r → Matrix a a ℝ) (hC : Continuous C)
    (hS : ∀ n, ∀ᵐ x ∂(P n : Measure (SpectralArray m)),
      (C (spectralBlockView m r x)).PosSemidef)
    (hS₀ : ∀ᵐ x ∂(P₀ : Measure (SpectralArray m)),
      (C (spectralBlockView m r x)).PosSemidef)
    (F : SpectralBlock m r × EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, ∫ z, F (spectralBlockView m r x, z)
        ∂multivariateGaussian 0 (C (spectralBlockView m r x))
        ∂(P n : Measure (SpectralArray m))) atTop
      (𝓝 (∫ x, ∫ z, F (spectralBlockView m r x, z)
        ∂multivariateGaussian 0 (C (spectralBlockView m r x))
        ∂(P₀ : Measure (SpectralArray m)))) := by
  obtain ⟨G, hG⟩ := cavity_gaussian_joint_test_extension F
  let b := spectralBlockView m r
  have hb : Continuous b := continuous_spectralBlockView m r
  let f : SpectralArray m →ᵇ ℝ :=
    G.compContinuous ⟨fun x => (b x, C (b x)), hb.prodMk (hC.comp hb)⟩
  have he (Q : ProbabilityMeasure (SpectralArray m))
      (hQ : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), (C (b x)).PosSemidef) :
      (∫ x, ∫ z, F (b x, z) ∂multivariateGaussian 0 (C (b x))
        ∂(Q : Measure (SpectralArray m))) = ∫ x, f x ∂(Q : Measure (SpectralArray m)) := by
    apply integral_congr_ae
    filter_upwards [hQ] with x hx
    exact (hG (b x) (C (b x)) hx).symm
  change Tendsto (fun n => ∫ x, ∫ z, F (b x, z) ∂multivariateGaussian 0 (C (b x))
      ∂(P n : Measure (SpectralArray m))) _
    (𝓝 (∫ x, ∫ z, F (b x, z) ∂multivariateGaussian 0 (C (b x))
      ∂(P₀ : Measure (SpectralArray m))))
  simp_rw [he _ hS₀, he _ (hS _)]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP f

end InvariantIsing

end

end OAI
