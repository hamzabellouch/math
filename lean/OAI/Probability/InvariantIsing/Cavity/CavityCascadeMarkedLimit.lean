import OAI.Probability.InvariantIsing.Cavity.CavityCascadeSpectralLimit
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianJointTest

namespace OAI

/-! Joint Gaussian marks and every synchronized finite overlap label
pass to the rounded-cascade limit, including singular covariances. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_cascade_marked_block_tendsto {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ProbabilityMeasure (SpectralArray m))
    (B : SpectralArray m → RealArray) (hB : Measurable B)
    (hGG : HasGhirlandaGuerra B (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), GramDiagonal 1 (B x))
    (hU : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), IsUltrametricArray (B x))
    (q : ℝ → ℝ) (hq : Monotone q) (hb : ∀ u, q u ∈ Icc (0 : ℝ) 1)
    (hp : (Q : Measure (SpectralArray m)).map (fun x => B x 0 1) = unitUniform.map q)
    (d : SpectralEntry m) (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (hf : ∀ a, Continuous (f a))
    (hdiag : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, x (i, i) a = d a)
    (hsync : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i j, i ≠ j →
      ∀ a, x (i, j) a = f a (B x i j))
    (r : ℕ) (C : SpectralBlock m r → Matrix ι ι ℝ) (hC : Continuous C)
    (hCS : ∀ n, ∀ᵐ x ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray),
      (C (cavitySynchronizedBlock d f (arrayBlock spinArray r x))).PosSemidef)
    (hCQ : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), (C (spectralBlockView m r x)).PosSemidef)
    (F : SpectralBlock m r × EuclideanSpace ℝ ι →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, ∫ z,
      F (cavitySynchronizedBlock d f (arrayBlock spinArray r x), z)
      ∂multivariateGaussian 0 (C (cavitySynchronizedBlock d f (arrayBlock spinArray r x)))
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray))
      atTop (𝓝 (∫ x, ∫ z, F (spectralBlockView m r x, z)
        ∂multivariateGaussian 0 (C (spectralBlockView m r x))
        ∂(Q : Measure (SpectralArray m)))) := by
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, C x), continuous_id.prodMk hC⟩
  have ht := cavity_cascade_spectral_block_tendsto Q B hB hGG hG hU q hq hb hp d f hf
    hdiag hsync r H
  have heS n : (∫ x, H (cavitySynchronizedBlock d f (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray)) =
      ∫ x, ∫ z, F (cavitySynchronizedBlock d f (arrayBlock spinArray r x), z)
        ∂multivariateGaussian 0 (C (cavitySynchronizedBlock d f (arrayBlock spinArray r x)))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray) :=
    integral_congr_ae ((hCS n).mono fun x hx => hExt _ _ hx)
  have heQ : (∫ x, H (spectralBlockView m r x) ∂(Q : Measure (SpectralArray m))) =
      ∫ x, ∫ z, F (spectralBlockView m r x, z)
        ∂multivariateGaussian 0 (C (spectralBlockView m r x))
        ∂(Q : Measure (SpectralArray m)) :=
    integral_congr_ae (hCQ.mono fun x hx => hExt _ _ hx)
  simpa only [heS, heQ] using ht

end InvariantIsing

end

end OAI
