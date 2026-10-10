import OAI.Probability.InvariantIsing.Cavity.CavityStrictCascadeLimit
import OAI.Probability.InvariantIsing.Cavity.CavityRecalculatedFiniteCascade

namespace OAI

/-! Strict finite overlap levels and recalculated covariance leave all
bounded Gaussian-marked spectral-block limits unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_strict_uniform_gaussian_error {m r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance k rho x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance k rho)⟩
  have hpos (n : ℕ) (a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1) :
      ∀ᵐ x ∂(cascadeCompactLaw n (uniformExponent n) a : Measure JointArray),
        (cavityGroupBlockCovariance k rho (B x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (uniformExponent n) a ha ha0 ha1
      (cavityCanonicalDiagonal rho lam hrho hsum p) (cavityCanonicalLabel rho lam hrho hsum p)
      (continuous_cavityCanonicalLabel rho lam hrho hsum p)
      (cavityCanonicalCoordinate_monotone rho lam hrho hsum p)
      (fun j => cavityCanonicalCoordinate_nonneg rho lam hrho hsum p j _)
      (fun j => cavityCanonicalCoordinate_le_diagonal rho lam hrho hsum p j _)
      rho (fun j => (hrho j).le)
  have he (n : ℕ) (a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1) :
      (∫ x, H (B x) ∂(cascadeCompactLaw n (uniformExponent n) a : Measure JointArray)) =
      ∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
        ∂(cascadeCompactLaw n (uniformExponent n) a : Measure JointArray) :=
    integral_congr_ae ((hpos n a ha ha0 ha1).mono (fun x hx => hExt _ _ hx))
  have hs n := he n (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i))
    ((cavityStrictUniformLevels_strict p n).monotone.comp (cavityFiniteLevel_monotone n))
    (cavityStrictUniformLevels_mem p n _).1.le (cavityStrictUniformLevels_mem p n _).2.le
  have hb n := he n (uniformCellAverage p n)
    (uniformCellAverage_monotone p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n)
    (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n 0).1
    (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n n).2
  have ht := cavity_strict_uniform_block_error rho lam hrho hsum p H
  simpa only [hs, hb, B] using ht

theorem cavity_strict_recalculated_gaussian_error {m r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p')
        (cavityCanonicalLabel rho lam hrho hsum p') (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B (cavityStrictUniformPath p n) x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B (cavityStrictUniformPath p n) x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B p x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  have hr := cavity_recalculated_finite_cascade_error rho lam hrho hsum p
    (cavityStrictUniformPath p) (cavityStrictUniformPath_l1_tendsto p)
    uniformExponent (fun n i => cavityStrictUniformLevels p n (cavityFiniteLevel n i))
    (fun n => (cavityStrictUniformLevels_strict p n).monotone.comp (cavityFiniteLevel_monotone n))
    (fun n => (cavityStrictUniformLevels_mem p n _).1.le)
    (fun n => (cavityStrictUniformLevels_mem p n _).2.le) F
  have hs := cavity_strict_uniform_gaussian_error rho lam hrho hsum p F
  simpa only [sub_add_sub_cancel, zero_add, B] using hr.add hs

end InvariantIsing

end

end OAI
