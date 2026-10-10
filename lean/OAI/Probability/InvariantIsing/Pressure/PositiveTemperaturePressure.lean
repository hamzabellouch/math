import OAI.Probability.InvariantIsing.Spectral.ScaledSpectralLaw

namespace OAI

/-! The conditional main theorem at every positive inverse temperature. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem positive_temperature_pressure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (β : ℝ) (hβ : 0 < β)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) :=
  limiting_pressure hhaar hgauss hpub P U hU hHaar (fun N i => β*eig N i)
    (scaledSpectralLaw ν β) (β*a) (β*b)
    (scaled_spectral_compact ν a b β hβ.le hbound)
    (scaled_spectral_support_bound ν a b β hβ.le hbound)
    (scaled_spectral_support_mem ν β a ha) (scaled_spectral_support_mem ν β b hb)
    (scaled_spectral_no_outliers eig a b β hβ hno) (scaled_spectral_weak eig ν β hweak)

end InvariantIsing

end

end OAI
