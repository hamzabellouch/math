import OAI.Probability.InvariantIsing.Magnetic.RestrictedFiniteLogEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledLog

namespace OAI

/-! The exact finite spectral trial value in the labeled coordinates
used for physical Haar replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_labeled_log_evaluation
    {m d N n : ℕ} (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
    let ν := cavityLabeledPriorKernel n (H n) (restrictedSpinPrior T hT)
    let V := cavityLabeledPotential n K L (c • 1)
    Integrable (fun ω => Real.log (∫ x, Real.exp (V (ω,x)) ∂ν ω)) P ∧
      (N : ℝ)⁻¹ * (∫ ω, Real.log (∫ x, Real.exp (V (ω,x)) ∂ν ω) ∂P) + (N : ℝ)⁻¹ * (Real.log T.card - N * Real.log 2) =
        constrainedBlockValue T h + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p := by
  intro hq0 h H S S₀ K L c P ν V
  have hv := restricted_cavity_finite_log_evaluation hN T hT rho lam hrho hsum B hB hBE hcomplete
    g a ha counts hcounts_le hcounts hcounts_rho p cut hcut hfirst hlast q hq hp htop
  have ht := cavity_labeled_log_mean n (chainExponent cut)
    (chainExponent_admissible hcut hfirst hlast) S₀ (H n) S K L (c • 1)
    (restrictedSpinPrior T hT) hv.1
  refine ⟨ht.1, ?_⟩
  rw [ht.2]
  exact hv.2

end InvariantIsing

end

end OAI
