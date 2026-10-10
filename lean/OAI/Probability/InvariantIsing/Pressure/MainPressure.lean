import OAI.Probability.InvariantIsing.Pressure.LimitingPressure
import OAI.Probability.InvariantIsing.Spectral.SpectralExtremeLimits

namespace OAI

/-! Theorem 1.1 with the manuscript's exact extreme-eigenvalue hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem limiting_pressure_of_extreme_limits
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b))
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) :=
  limiting_pressure hhaar hgauss hpub P U hU hHaar eig ν a b hcompact hbound ha hb
    (spectral_no_outliers_of_extreme_limits eig a b hmin hmax) hweak

end InvariantIsing

end

end OAI
