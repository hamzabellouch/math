import OAI.Probability.InvariantIsing.Pressure.GroundStateLimit
import OAI.Probability.InvariantIsing.Spectral.SpectralExtremeLimits

namespace OAI

/-! The ground-state corollary under the manuscript's exact extreme-eigenvalue hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem ground_state_limit_of_extreme_limits
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b))
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    ∃ M : ℝ,
      Tendsto (fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P)
        atTop (𝓝 M) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹))
        atTop (𝓝 M)) ∧
      Tendsto (thermalVariationalValue ν b) atTop (𝓝 M) :=
  ground_state_limit hhaar hgauss hpub P U hU hHaar eig ν a b hbound ha hb
    (spectral_no_outliers_of_extreme_limits eig a b hmin hmax) hweak

end InvariantIsing

end

end OAI
