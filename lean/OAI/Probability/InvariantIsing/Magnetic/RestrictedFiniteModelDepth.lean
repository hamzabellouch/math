import OAI.Probability.InvariantIsing.Cavity.CavityFiniteModelSpinTest
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFiniteDepthTest
import OAI.Probability.InvariantIsing.Fields.PriorLabeledDepthMean

namespace OAI

/-! Common-depth preservation in the actual normalized finite spectral model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_model_depth_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
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
    (∫ ω, priorCavityLabeledDepthMean n K (H n) L (c • 1) (restrictedSpinPrior T hT)
      (fun i => Φ (q (fieldDepthLevel h i))) ω
      ∂cavityLabeledDisorderLaw n (chainExponent cut) S₀ S) =
      ∫ t, Φ (p t) ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
  have hI := cavity_finite_original_integrability rho lam hrho hsum B hB g a ha
    p cut hcut hfirst hlast q hq hp htop L (c • 1) (restrictedSpinPrior T hT)
  have hAtom (i : ℕ) (hi : i < n) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)) :=
    cavityFiniteNoiseCovariance_atomless rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop hd i hi
  rw [integral_priorCavityLabeledDepthMean n (chainExponent cut) K (H n) S₀ S L (c • 1) (restrictedSpinPrior T hT)
    (chainExponent_admissible hcut hfirst hlast) hAtom hI]
  rw [← cavity_rooted_depth_test_disintegration n K (H n) L (c • 1)
    (restrictedSpinPrior T hT) _ _ (fun i => hΦ (q (fieldDepthLevel h i)))]
  exact restricted_cavity_finite_depth_test hpub hd hN T hT rho lam hrho hsum B hB hBE hcomplete
    g a ha p cut hcut hfirst hlast q hq hp htop Φ hΦ

end InvariantIsing

end

end OAI
