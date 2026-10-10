import OAI.Probability.InvariantIsing.Cavity.CavityFiniteModelSpinTest
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledSpinObservable

namespace OAI

/-! The normalized spectral-block spin observable has exactly the
finite scalar-field value needed for the physical cavity limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_finite_normalized_spin_test (hpub : PanchenkoTalagrandFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
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
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ) (hΦc : Continuous Φ) (j : Fin N)
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
    (∫ ω, cavityWeightedReplicaMean
      (cavityLabeledPriorKernel n (H n) (uniformSpinPrior N) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L (c • 1) (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavitySpinObservable Φ hΦc j) (ω,ξ))
      ∂cavityLabeledDisorderLaw n (chainExponent cut) S₀ S) =
      ∫ t, Φ (p t) * fieldMagnetizationPath h t ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
  have hqmem := fun i => finite_overlap_value_mem_unit p cut hcut q hp i
  simp_rw [cavity_labeled_spin_observable rho lam hrho hsum p q hqmem K (H n) L
    (c • 1) Φ hΦc j]
  exact cavity_finite_model_spin_test hpub hd hN rho lam hrho hsum B hB hBE hcomplete
    g a ha p cut hcut hfirst hlast q hq hp htop Φ j hΦ

end InvariantIsing

end

end OAI
