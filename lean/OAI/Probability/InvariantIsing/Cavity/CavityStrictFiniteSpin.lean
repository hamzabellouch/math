import OAI.Probability.InvariantIsing.Cavity.CavityFiniteNormalizedSpin
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteExponentLaw

namespace OAI

/-! The actual normalized finite spin identity on the strict uniform
approximants. All finite partition and nondegeneracy premises are proved. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

def cavityStrictUniformField {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (n : ℕ) : FieldStep :=
  cavityFieldStep rho lam hrho hsum (cavityStrictUniformPath p n)
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (cavityStrictUniformLevels p n) (cavityStrictUniformLevels_strict p n).monotone
    (fun i => (cavityStrictUniformLevels_mem p n i).1.le)

theorem cavity_strict_finite_spin_test (hpub : PanchenkoTalagrandFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (Φ : ℝ → ℝ) (hΦc : Continuous Φ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let q := cavityStrictUniformLevels p n
    let p' := cavityStrictUniformPath p n
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p' q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p' (uniformCut n) q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p' q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ ω, cavityWeightedReplicaMean
      (cavityLabeledPriorKernel n (H n) (uniformSpinPrior N) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L (c • 1) (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p' q)
        (cavitySpinObservable Φ hΦc j) (ω,ξ))
      ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n)) S₀ S) =
      ∫ t, Φ (p' t) * fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) t
        ∂pathMeasure := by
  exact cavity_finite_normalized_spin_test hpub hd hN rho lam hrho hsum B hB hBE hcomplete
    g a ha (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (fun i s hs => cavityStrictUniformPath_on_cell p n i hs)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 Φ hΦc j hΦ

end InvariantIsing

end

end OAI
