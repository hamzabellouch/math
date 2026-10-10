import OAI.Probability.InvariantIsing.Magnetic.MagneticCompactPartition
import OAI.Probability.InvariantIsing.Magnetic.MagneticPartitionContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralApproximationSqueeze

namespace OAI

/-! The finite external-field formula for an arbitrary compact spectral law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem compact_spectral_field_pressure_tendsto_of_mem
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (heig : ∀ N i, eig N i∈Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) := by
  let δ := fun k : ℕ => (1 : ℝ)/(k+1)
  let D (k : ℕ) : CompactSpectralPartition ν a b (δ k) := Classical.choice
    (exists_compact_spectral_partition ν a b (δ k) hcompact hbound (by dsimp [δ]; positivity))
  have hab : a ≤ b := (hbound ha).2
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hL := compact_partition_magnetic_tendsto ν a b δ D hab ha hb hbound hδ γ c
    (fun a => (hγ a).le) hγsum
  apply spectral_approximation_squeeze _
    (fun k N => ∫ V, rotatedPressure (fun i => (D k).lowerValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
    (fun k N => ∫ V, rotatedPressure (fun i => (D k).upperValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
    (fun k => (finiteMagneticFunctional (measureR ((D k).law : Measure ℝ) (D k).edge) γ c).toReal)
    δ _ hL hδ
    (fun k => ((D k).field_pressure_tendsto hhaar hgauss hpub μ eig hweak group γ c hγ hγsum hgroup).1)
    (fun k => ((D k).field_pressure_tendsto hhaar hgauss hpub μ eig hweak group γ c hγ hγsum hgroup).2)
  intro k
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (D k).mean_field_pressure_bounds (by omega) (μ N) (eig N) ha hb hab (heig N) (fun i => c (group N i))

end InvariantIsing

end

end OAI
