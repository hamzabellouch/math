import OAI.Probability.InvariantIsing.Fields.ZeroFieldPopulations

namespace OAI

/-! The finite-field pressure theorem permits labels with zero limiting mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators Classical
namespace InvariantIsing

theorem general_spectral_mean_field_positive_part_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1))) atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (fallback : {a // 0 < γ a})
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b)
        (fun i : {a // 0 < γ a} => γ i) (fun i => c i)).toReal) := by
  have hpos : Tendsto (fun N i =>
      (spinGroupSize (positiveSpectralLabel γ fallback ∘ group N) i : ℝ)/N)
      atTop (𝓝 (fun i : {a // 0 < γ a} => γ i)) :=
    by
      have hp := positive_spectral_counts_tendsto id group γ hγ fallback
        (by simpa only [spectralLabelCount_eq_spinGroupSize,id_eq] using hgroup)
      simpa only [spectralLabelCount_eq_spinGroupSize,id_eq] using hp
  have hp := general_spectral_mean_field_pressure_tendsto hhaar hgauss hpub μ eig ν a b
    hcompact hbound ha hb hno hweak (fun N => positiveSpectralLabel γ fallback ∘ group N)
    (fun i : {a // 0 < γ a} => γ i) (fun i => c i) (fun i => i.property)
    (positiveSpectralWeights_sum γ hγ hγsum) hpos
  have he := physical_mean_zero_field_populations μ eig group γ c hγ fallback hgroup
  have hh := he.add hp
  simpa only [sub_add_cancel,zero_add,positiveFieldProjection,Function.comp_apply] using hh

end InvariantIsing

end

end OAI
