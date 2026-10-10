import OAI.Probability.InvariantIsing.Spectral.CompactPartitionPressure
import OAI.Probability.InvariantIsing.Spectral.CompactPartitionContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralApproximationSqueeze

namespace OAI

/-! The zero-field pressure limit for arbitrary compact spectral laws,
when the finite spectra lie between the limiting support edges. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem compact_spectral_pressure_tendsto_of_mem
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (heig : ∀ N i, eig N i∈Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  let δ := fun k : ℕ => (1 : ℝ)/(k+1)
  let D (k : ℕ) : CompactSpectralPartition ν a b (δ k) := Classical.choice
    (exists_compact_spectral_partition ν a b (δ k) hcompact hbound (by dsimp [δ]; positivity))
  have hab : a ≤ b := (hbound ha).2
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hL := compact_partition_variational_tendsto ν a b δ D hab ha hb hbound hδ
  apply spectral_approximation_squeeze _
    (fun k N => ∫ V, rotatedPressure (fun i => (D k).lowerValue (eig N i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
    (fun k N => ∫ V, rotatedPressure (fun i => (D k).upperValue (eig N i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
    (fun k => (variationalFunctional (measureR ((D k).law : Measure ℝ) (D k).edge)).toReal)
    δ _ hL hδ
    (fun k => ((D k).pressure_tendsto hhaar hgauss hpub μ eig hweak).1)
    (fun k => ((D k).pressure_tendsto hhaar hgauss hpub μ eig hweak).2)
  intro k
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (D k).mean_pressure_bounds (by omega) (μ N) (eig N) ha hb hab (heig N)

end InvariantIsing

end

end OAI
