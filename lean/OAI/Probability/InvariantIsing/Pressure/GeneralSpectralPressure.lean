import OAI.Probability.InvariantIsing.Spectral.CompactSpectralPressure
import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! The general compact spectral law and no-outlier mean-pressure theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem general_spectral_mean_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hab : a ≤ b := (hbound ha).2
  have hc := compact_spectral_pressure_tendsto_of_mem hhaar hgauss hpub μ
    (fun N i => spectralClip a b (eig N i)) ν a b hcompact hbound ha hb
    (fun N i => spectralClip_mem hab (eig N i))
    (spectral_clip_empirical_tendsto eig ν a b hbound hweak)
  have hη := spectralExcess_tendsto eig a b hno
  have hd : Tendsto (fun N =>
      (∫ V, rotatedPressure (fun i => spectralClip a b (eig N i))
        (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)-
      ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [zero_div] using hη.div_const 2)
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [Real.norm_eq_abs] using spectral_clip_mean_pressure_close (by omega)
      (μ N) (eig N) a b (spectralExcess (eig N) a b) hab
      (spectralExcess_nonneg _ _ _) (spectralExcess_bounds _ _ _)
  have hh := hc.sub hd
  simpa only [sub_sub_cancel,sub_zero] using hh

end InvariantIsing

end

end OAI
