import OAI.Probability.InvariantIsing.Cavity.CavityFiniteLabeledLog
import OAI.Probability.InvariantIsing.Cavity.CavityPreliminaryLower
import OAI.Probability.InvariantIsing.Cavity.CavityStrictFiniteSpin

namespace OAI

/-! The preliminary logarithmic lower bound in the manuscript's exact
finite-field trial-value coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_finite_trial_preliminary_lower
    {m d N : ℕ} (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (U : Rotation N)
    (A : ℕ → ℝ) (cap : ℝ → ℕ → ℝ) (hu : ∀ T > 0, ∀ n, cap T n ≤ A n) :
    let p' := cavityStrictUniformPath p
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance rho lam hrho hsum g (p' n) (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g (p' n) (uniformCut n)
        (cavityStrictUniformLevels p n))
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath rho lam hrho hsum g (p' n) (cavityStrictUniformLevels p n) n)
      (uniformSpinPrior N)
    (∀ T > 0, Tendsto (fun n => cap T n -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential n K L (c • 1) (ω,x)) T)
        ∂η n ω) ∂Q n) atTop (𝓝 0)) →
    ∀ ε > 0, ∀ᶠ n in atTop,
      fieldValue (cavityStrictUniformField rho lam hrho hsum p n) 0 +
        fieldPairing (p' n) (cavityStrictUniformField rho lam hrho hsum p n) / 2 +
        spectralFunctional (finiteR rho lam hrho hsum) (p' n) - (N : ℝ)⁻¹ * A n < ε := by
  intro p' K L c Q η hcap ε hε
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hlower := cavity_finite_preliminary_lower rho lam hrho hsum B hB g a ha p
    L (c • 1) (uniformSpinPrior N) A cap hu hcap
  filter_upwards [hlower (ε * N) (mul_pos hε hn)] with j hj
  have hv := cavity_finite_labeled_log_evaluation hN rho lam hrho hsum B hB hBE hcomplete
    g a ha counts hcounts_le hcounts hcounts_rho (p' j) (uniformCut j) (uniformCut_strict j)
    (uniformCut_zero j) (uniformCut_last j) (cavityStrictUniformLevels p j)
    (cavityStrictUniformLevels_strict p j) (cavityStrictUniformPath_on_cell p j)
    (cavityStrictUniformLevels_mem p j (Fin.last j)).2 U
  have he : (N : ℝ)⁻¹ *
      (∫ ω, Real.log (∫ x, Real.exp (cavityLabeledPotential j K L (c • 1) (ω,x)) ∂η j ω) ∂Q j) =
      fieldValue (cavityStrictUniformField rho lam hrho hsum p j) 0 +
        fieldPairing (p' j) (cavityStrictUniformField rho lam hrho hsum p j) / 2 +
        spectralFunctional (finiteR rho lam hrho hsum) (p' j) := hv.2
  calc
    _ = (N : ℝ)⁻¹ * ((∫ ω, Real.log
        (∫ x, Real.exp (cavityLabeledPotential j K L (c • 1) (ω,x)) ∂η j ω) ∂Q j) - A j) := by
      rw [mul_sub, he]
    _ < (N : ℝ)⁻¹ * (ε * N) := mul_lt_mul_of_pos_left hj (inv_pos.mpr hn)
    _ = ε := by field_simp

end InvariantIsing

end

end OAI
