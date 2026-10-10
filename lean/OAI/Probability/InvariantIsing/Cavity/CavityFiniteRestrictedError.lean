import OAI.Probability.InvariantIsing.Cavity.CavityFiniteTiltedTail
import OAI.Probability.InvariantIsing.Cavity.CavityFinitePriorMoment
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledRestrictedModel
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactorIndicator
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedAverage
import OAI.Probability.InvariantIsing.Cavity.CavityPriorFourthTail

namespace OAI

/-! Cutoff-removal errors for the finite spectral cavity law, controlled
by uniform prior and full-Gibbs moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix Matrix.Norms.L2Operator BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_error {m d N n k r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B₀ : Matrix (Fin (m*N)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (O : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (T : ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ) :
    let K := B₀.transpose * cavityRepeatedSpectrum (n := N) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n) n
    let Q := cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    cavityFactorSize K L C * (1+B^2) ≤ T →
    |(∫ ω, cavityRegularizedReplicaMean (cavityLabeledPriorKernel n R π ω)
        (fun x => cavityLabeledRestrictedWeight n K L C T B (ω,x))
        (fun σ => cavityLabeledReplicaTest O F (ω,σ)) δ ∂Q) -
      ∫ ω, cavityWeightedReplicaMean (cavityLabeledPriorKernel n R π ω)
        (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (fun σ => cavityLabeledReplicaTest O F (ω,σ)) ∂Q| ≤
      ‖F‖ * r * δ / (Real.exp (-cavityFactorSize K L C * (1+B^2)) / 2) +
        4 * ‖F‖ * (cavityGaussianLinearMomentBound d 4 0 (∑ a, (ρ a)⁻¹) / B^4) +
        2 * ‖F‖ * r * (cavityGaussianLinearMomentBound d 2
          (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ / B^2) := by
  intro K R Q hT
  let η := cavityLabeledPriorKernel n R π
  let H := cavityLabeledPotential n K L C
  let Z := fun z : CavityLabeledDisorder d n × CavityLabeledState d k n =>
    ‖(cavityLabeledEndpoint n z).1‖
  let V := cavityLabeledReplicaTest (d := d) O F
  have hH : Measurable H := measurable_cavityLabeledPotential n K L C
  have hZ : Measurable Z := (measurable_cavityLabeledEndpoint n).fst.norm
  have hV : Measurable V := measurable_cavityLabeledReplicaTest O F
  have hm := cavity_finite_labeled_moment ρ eig hρ hsum B₀ hB₀ g a ha
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π 2
  have hp := cavity_finite_prior_fourth_moment ρ eig hρ hsum g
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 π
  have ht := cavity_random_prior_fourth_tail Q (fun ω => η ω) η.measurable Z hZ
    hp.1 hp.2.1 hB hp.2.2
  have hsq := cavity_finite_labeled_square_tail ρ eig hρ hsum B₀ hB₀ g a ha
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π hB
  have he := cavity_radial_restricted_regularized_error Q (fun ω => η ω) η.measurable
    H Z hH hZ (hm.1.mono fun _ h => h.1) V hV (a := B)
    (cavityFactorSize_nonneg K L C) (norm_nonneg F) hδ
    (fun ω x => cavity_logFactor_growth K L C _ _)
    (fun ω σ => (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _))
  have hw ω : {x | |Z (ω,x)| ≤ B}.indicator (fun x => Real.exp (H (ω,x))) =
      fun x => cavityLabeledRestrictedWeight n K L C T B (ω,x) := by
    funext x
    simpa only [Z,abs_norm,H,cavityLabeledPotential,cavityLabeledRestrictedWeight,
      Function.comp_apply] using
      (cavityRestrictedFactor_eq_indicator K L C T hB.le hT
        (fun x => (cavityLabeledEndpoint n (ω,x)).1)
        (fun x => (cavityLabeledEndpoint n (ω,x)).2) x).symm
  rw [show -cavityFactorSize K L C * (1+B^2) = -(cavityFactorSize K L C * (1+B^2)) by ring] at he
  simp only [hw] at he
  have hsq' : (∫ ω, ((η ω).tilted (fun x => H (ω,x))).real
      {x | B < |Z (ω,x)|} ∂Q) ≤ cavityGaussianLinearMomentBound d 2
        (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ / B^2 := by
    simpa only [Z,abs_norm,H,η,R,Q,K] using hsq
  have hout := he.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 4*‖F‖)))
    (mul_le_mul_of_nonneg_left hsq' (by positivity : 0 ≤ 2*‖F‖*r)))
  simpa only [η,H,V,neg_mul] using hout

end InvariantIsing

end

end OAI
