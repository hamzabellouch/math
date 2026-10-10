import OAI.Probability.InvariantIsing.Pressure.GeneralSpectralPressure

namespace OAI

/-! Expectations on an arbitrary probability space carrying the physical Haar matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

lemma measurable_physicalPressure {N : ℕ} (hN : 0 < N) (eig c : Fin N → ℝ) :
    Measurable (fun U : Orthogonal N => rotatedPressure eig (matrixRotation U⁻¹) c) := by
  have hm := (measurable_rotatedPressure eig c).comp
    ((measurable_cavityOrientationLift hN).comp measurable_inv)
  convert hm using 1
  funext U
  simp only [Function.comp_apply,rotatedPressure,cavityOrientationLift_energy]

lemma physicalPressure_integral_map {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) (U : Ω → Orthogonal N) (hU : Measurable U)
    (eig c : Fin N → ℝ) :
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂P.map U)=
      ∫ ω, rotatedPressure eig (matrixRotation (U ω)⁻¹) c ∂P :=
  integral_map hU.aemeasurable (measurable_physicalPressure hN eig c).aestronglyMeasurable

theorem physical_mean_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  let μ := fun N => P.map (U N)
  let (N : ℕ) : IsProbabilityMeasure (μ N) :=
    (Measure.isProbabilityMeasure_map_iff (hU N).aemeasurable).mpr inferInstance
  let (N : ℕ) : (μ N).IsMulRightInvariant := hHaar N
  have hh := general_spectral_mean_pressure_tendsto hhaar hgauss hpub μ eig ν a b
    hcompact hbound ha hb hno hweak
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact physicalPressure_integral_map (by omega) P (U N) (hU N) (eig N) (fun _ => 0)

end InvariantIsing

end

end OAI
