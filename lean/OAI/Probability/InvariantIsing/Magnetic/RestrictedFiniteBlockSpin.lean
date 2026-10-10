import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariancePath
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFiniteSpinTest
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRootedBlock

namespace OAI

/-! The full quadratic cavity spin test specialized to a genuine finite
spectral law and overlap quantile. All matrix and scalar covariance
hypotheses of the marking calculation are discharged here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_block_spin_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ σ, cavityRootedBlockDepthTest (fun i => Φ (q (fieldDepthLevel h i))) σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT))
        (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
              (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)))) =
      ∫ t, Φ (p t) * restrictedBlockOverlapPath hN T hT h t ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
  let M : Measure (ℕ → CavitySpinState d N n) :=
    (probabilityReplicaKernel
      (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT))
      (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT)).measurable)
        ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
            (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
  have hM : IsProbabilityMeasure M := by
    dsimp only [M]
    infer_instance
  have he := @restricted_rooted_block_evaluation d N hN T hT h M hM q Φ C hΦ
  have hindex : ∀ᵐ t ∂pathMeasure, q (fieldLevelIndex h t) = p t := by
    filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with t ht
    obtain ⟨i, hi⟩ := ht
    rw [fieldLevelIndex_on_cell h i hi, hp i t hi]
  refine (he ?_).trans ?_
  · intro j
    have hj := restricted_cavity_finite_spin_test hpub hd hN T hT rho lam hrho hsum B hB
      hBE hcomplete g a ha p cut hcut hfirst hlast q hq hp htop Φ j hΦ
    apply hj.trans
    apply integral_congr_ae
    filter_upwards [hindex] with t ht
    rw [ht]
  · apply integral_congr_ae
    filter_upwards [hindex] with t ht
    rw [ht]

end InvariantIsing

end

end OAI
