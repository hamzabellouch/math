import OAI.Probability.InvariantIsing.Spectral.SelectedPartitionPressure
import OAI.Probability.InvariantIsing.Spectral.CompactPartitionContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralApproximationSqueeze

namespace OAI

/-! Compact spectral pressure along arbitrary diverging dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem selected_compact_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (eig : (k : ℕ) → Fin (N k) → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (heig : ∀ k i, eig k i∈Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hN k) (eig k)) atTop (𝓝 ν)) :
    Tendsto (fun k => ∫ V, rotatedPressure (eig k) (matrixRotation V⁻¹) (fun _ => 0) ∂μ (N k))
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  let δ := fun k : ℕ => (1 : ℝ)/(k+1)
  let D (k : ℕ) : CompactSpectralPartition ν a b (δ k) := Classical.choice
    (exists_compact_spectral_partition ν a b (δ k) hcompact hbound (by dsimp [δ]; positivity))
  have hab : a ≤ b := (hbound ha).2
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hL := compact_partition_variational_tendsto ν a b δ D hab ha hb hbound hδ
  apply spectral_approximation_squeeze _
    (fun j k => ∫ V, rotatedPressure (fun i => (D j).lowerValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (N k))
    (fun j k => ∫ V, rotatedPressure (fun i => (D j).upperValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (N k))
    (fun j => (variationalFunctional (measureR ((D j).law : Measure ℝ) (D j).edge)).toReal)
    δ _ hL hδ
    (fun j => ((D j).selected_pressure_tendsto hhaar hgauss hpub μ N hN hNlim eig hweak).1)
    (fun j => ((D j).selected_pressure_tendsto hhaar hgauss hpub μ N hN hNlim eig hweak).2)
  intro j
  exact Filter.Eventually.of_forall fun k =>
    (D j).mean_pressure_bounds (hN k) (μ (N k)) (eig k) ha hb hab (heig k)

end InvariantIsing

end

end OAI
