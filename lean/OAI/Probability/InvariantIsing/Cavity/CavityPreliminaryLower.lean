import OAI.Probability.InvariantIsing.Cavity.CavityFiniteLogCap
import OAI.Probability.InvariantIsing.Cavity.CavityStrictUniformPath

namespace OAI

/-! One-sided removal of the logarithmic cap. Only the limiting finite
model needs full moments; the finite physical increment is bounded below
by each of its capped approximations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_preliminary_lower_of_caps
    (A B : ℕ → ℝ) (C D : ℝ → ℕ → ℝ) {K : ℝ}
    (hupper : ∀ T > 0, ∀ n, C T n ≤ A n)
    (herror : ∀ T > 0, ∀ n, |B n - D T n| ≤ K / T)
    (hcap : ∀ T > 0, Tendsto (fun n => C T n - D T n) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, B n - A n < ε := by
  intro ε hε
  let T := 1 + 2 * |K| / ε
  have hT : 0 < T := by dsimp only [T]; positivity
  have hKT : K / T < ε / 2 := by
    apply (div_lt_iff₀ hT).mpr
    have he : T * ε = ε + 2 * |K| := by dsimp only [T]; field_simp
    nlinarith [le_abs_self K]
  filter_upwards [(hcap T hT).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 2 by positivity))] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  have he := (le_abs_self (B n - D T n)).trans (herror T hT n)
  have hc := neg_abs_le (C T n - D T n)
  have hu := hupper T hT n
  linarith

theorem cavity_finite_preliminary_lower {m d N k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (A : ℕ → ℝ) (cap : ℝ → ℕ → ℝ) (hu : ∀ T > 0, ∀ n, cap T n ≤ A n) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let G := fun n => cavityLabeledPotential n K L C
    (∀ T > 0, Tendsto (fun n => cap T n -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂η n ω) ∂Q n)
      atTop (𝓝 0)) →
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∫ ω, Real.log (∫ x, Real.exp (G n (ω,x)) ∂η n ω) ∂Q n) - A n < ε := by
  intro K Q η G hcap
  apply cavity_preliminary_lower_of_caps A
    (fun n => ∫ ω, Real.log (∫ x, Real.exp (G n (ω,x)) ∂η n ω) ∂Q n) cap
    (fun T n => ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂η n ω) ∂Q n)
    (K := 2 * (cavityFactorSize K L C)^2 *
      (1 + cavityGaussianLinearMomentBound d 4
        (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹)) hu _ hcap
  intro T hT n
  exact (cavity_finite_log_cap ρ eig hρ hsum B hB g a ha
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π hT).2.2

end InvariantIsing

end

end OAI
