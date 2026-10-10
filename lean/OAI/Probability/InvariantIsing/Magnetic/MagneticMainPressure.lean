import OAI.Probability.InvariantIsing.Magnetic.MagneticLimitingPressure
import OAI.Probability.InvariantIsing.Spectral.SpectralExtremeLimits

namespace OAI

/-! The finite-field clause of Theorem7.1 with the exact manuscript
spectral-edge assumptions, in expectation and almost surely. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem limiting_finite_field_pressure_of_extreme_limits
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
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun i => c (group N i)) ∂P)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun i => c (group N i)))
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) :=
  limiting_finite_field_pressure hhaar hgauss hpub P U hU hHaar eig ν a b hcompact hbound ha hb
    (spectral_no_outliers_of_extreme_limits eig a b hmin hmax) hweak group γ c hγ hγsum hgroup

end InvariantIsing

end

end OAI
