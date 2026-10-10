import OAI.Probability.InvariantIsing.Cavity.CavityRecalculatedLabels
import OAI.Probability.InvariantIsing.Cavity.CavityGroupBlockGaussian

namespace OAI

/-! The finite-cascade Gaussian covariance can be recalculated with the
approximating path before taking its replica limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_recalculated_gaussian_cascade_error {m r k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p')
        (cavityCanonicalLabel ρ eig hρ hρsum p') (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B (q n) x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B (q n) x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  let P n := cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n)
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance k ρ x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance k ρ)⟩
  have hpos (n : ℕ) (p' : OverlapPath) : ∀ᵐ x ∂(P n : Measure JointArray),
      (cavityGroupBlockCovariance k ρ (B p' x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (uniformExponent n) (uniformCellAverage p n)
      (uniformCellAverage_monotone p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n)
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n 0).1
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n n).2
      (cavityCanonicalDiagonal ρ eig hρ hρsum p') (cavityCanonicalLabel ρ eig hρ hρsum p')
      (continuous_cavityCanonicalLabel ρ eig hρ hρsum p')
      (cavityCanonicalCoordinate_monotone ρ eig hρ hρsum p')
      (fun a => cavityCanonicalCoordinate_nonneg ρ eig hρ hρsum p' a _)
      (fun a => cavityCanonicalCoordinate_le_diagonal ρ eig hρ hρsum p' a _)
      ρ (fun a => (hρ a).le)
  have hi (n : ℕ) (p' : OverlapPath) : Integrable (fun x => H (B p' x)) (P n : Measure JointArray) := by
    let J : JointArray →ᵇ ℝ := H.compContinuous
      ⟨B p', (continuous_cavitySynchronizedBlock _ _
        (continuous_cavityCanonicalLabel ρ eig hρ hρsum p')).comp (by
          unfold arrayBlock spinArray
          fun_prop)⟩
    exact J.integrable _
  have he (n : ℕ) (p' : OverlapPath) :
      (∫ x, H (B p' x) ∂(P n : Measure JointArray)) =
        ∫ x, ∫ z, F (B p' x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p' x))
          ∂(P n : Measure JointArray) :=
    integral_congr_ae ((hpos n p').mono (fun x hx => hExt _ _ hx))
  have ht := cavity_recalculated_label_integral_error ρ eig hρ hρsum p q hL P H
  change Tendsto (fun n => ∫ x, H (B (q n) x) - H (B p x) ∂(P n : Measure JointArray))
    atTop (𝓝 0) at ht
  have hid n : (∫ x, H (B (q n) x) - H (B p x) ∂(P n : Measure JointArray)) =
      (∫ x, ∫ z, F (B (q n) x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B (q n) x))
        ∂(P n : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p x))
        ∂(P n : Measure JointArray) := by
    rw [integral_sub (hi n (q n)) (hi n p), he, he]
  simpa only [hid] using ht

end InvariantIsing

end

end OAI
