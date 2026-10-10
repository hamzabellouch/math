import OAI.Probability.InvariantIsing.Magnetic.MagneticWassersteinPressure
import OAI.Probability.InvariantIsing.Spectral.SpectralExtremeLimits

namespace OAI

/-! Full Theorem7.1 with the manuscript spectral-edge and W1 field assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem limiting_wasserstein_field_pressure_of_extreme_limits
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
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
      atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (hw : Tendsto (fun k => fieldWassersteinOne (empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) ξ)
      atTop (𝓝 0)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N) ∂P)
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) :=
  limiting_wasserstein_field_pressure hhaar hgauss hpub P U hU hHaar eig ν a b hcompact hbound ha hb
    (spectral_no_outliers_of_extreme_limits eig a b hmin hmax) hweak field ξ hξ hw

end InvariantIsing

end

end OAI
