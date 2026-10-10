import OAI.Probability.InvariantIsing.Cavity.CavityRandomTiltMoment
import OAI.Probability.InvariantIsing.Cavity.CavityCappedLogIntegrable
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteLabeledMoment
import OAI.Probability.InvariantIsing.Cavity.CavityFinitePriorMoment

namespace OAI

/-! Uniform removal of the upper energy cap for the actual finite spectral
cavity logarithmic normalizer. No moment assumptions remain in this estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_log_cap {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] {T : ℝ} (hT : 0 < T) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let P := cavityLabeledDisorderLaw n (chainExponent cut)
      (cavityFiniteRootCovariance ρ eig hρ hsum g p q)
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q)
    let ν := cavityLabeledPriorKernel n R π
    let H := cavityLabeledPotential n K L C
    Integrable (fun ω => Real.log (∫ x, Real.exp (H (ω,x)) ∂ν ω)) P ∧
    Integrable (fun ω => Real.log (∫ x, Real.exp (min (H (ω,x)) T) ∂ν ω)) P ∧
    |(∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν ω) ∂P) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H (ω,x)) T) ∂ν ω) ∂P| ≤
      2 * (cavityFactorSize K L C)^2 *
        (1 + cavityGaussianLinearMomentBound d 4
          (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹) / T := by
  intro K R P ν H
  let Z := fun z : CavityLabeledDisorder d n × CavityLabeledState d k n =>
    ‖(cavityLabeledEndpoint n z).1‖
  have hH : Measurable H := measurable_cavityLabeledPotential n K L C
  have hg : ∀ ω x, |H (ω,x)| ≤ cavityFactorSize K L C * (1 + Z (ω,x)^2) :=
    fun ω x => cavity_logFactor_growth K L C _ _
  have ht := cavity_finite_labeled_moment ρ eig hρ hsum B hB g a ha
    p cut hcut hfirst hlast q hq hp htop L C π 4
  have hp4 := cavity_finite_prior_fourth_moment ρ eig hρ hsum g
    p cut hcut hfirst hlast q hq hp htop π
  have he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω) :=
    ht.1.mono fun _ h => h.1
  have henergy := cavity_random_quadratic_tilted_moment P ν ν.measurable H Z hH he
    (ht.1.mono fun _ h => h.2) ht.2.1 (cavityFactorSize_nonneg K L C) hg ht.2.2
  have hc := cavity_capped_log_integrable_ae P ν ν.measurable H Z hH
    hp4.1 hp4.2.1 (cavityFactorSize_nonneg K L C) hT.le hg
  exact ⟨cavity_full_log_integrable P ν ν.measurable H hH he
      henergy.1 henergy.2.1 hT hc, hc,
    cavity_log_cap_expectation_error P ν ν.measurable H hH he
      henergy.1 henergy.2.1 henergy.2.2 hT hc⟩

end InvariantIsing

end

end OAI
