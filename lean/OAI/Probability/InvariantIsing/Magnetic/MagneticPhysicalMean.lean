import OAI.Probability.InvariantIsing.Magnetic.MagneticGeneralSpectrum
import OAI.Probability.InvariantIsing.Pressure.PhysicalPressureMean

namespace OAI

/-! The finite-field mean formula on the original probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem physical_mean_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun i => c (group N i)) ∂P)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) := by
  let μ := fun N => P.map (U N)
  let (N : ℕ) : IsProbabilityMeasure (μ N) :=
    (Measure.isProbabilityMeasure_map_iff (hU N).aemeasurable).mpr inferInstance
  let (N : ℕ) : (μ N).IsMulRightInvariant := hHaar N
  have hh := general_spectral_mean_field_pressure_tendsto hhaar hgauss hpub μ eig ν a b
    hcompact hbound ha hb hno hweak group γ c hγ hγsum hgroup
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact physicalPressure_integral_map (by omega) P (U N) (hU N) (eig N) (fun i => c (group N i))

end InvariantIsing

end

end OAI
