import OAI.Probability.InvariantIsing.Core.FiniteTypePressure
import OAI.Probability.InvariantIsing.Spectral.PositiveSpectralPartition

namespace OAI

/-! A null-boundary spectral partition gives the physical pressure limit,
with its zero-mass cells assigned to a chosen positive-mass cell. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical BigOperators Function

namespace InvariantIsing

theorem spectral_partition_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (hbd : ∀ i, (ν : Measure ℝ) (frontier (S i))=0)
    (lam : ι → ℝ) (fallback aMax : {i // 0 < (ν : Measure ℝ).real (S i)})
    (hMax : ∀ a : {i // 0 < (ν : Measure ℝ).real (S i)}, lam a ≤ lam aMax) :
    Tendsto (fun N => ∫ V, rotatedPressure
      (fun i => lam (positiveSpectralLabel (fun a => (ν : Measure ℝ).real (S a)) fallback
        (spectralPartitionIndex S hcover (eig N i))))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N) atTop
      (𝓝 (variationalFunctional (measureR
        (finiteSpectralMeasure (fun i : {i // 0 < (ν : Measure ℝ).real (S i)} =>
          (ν : Measure ℝ).real (S i)) (fun i => lam i)) (lam aMax))).toReal) := by
  let w := fun a => (ν : Measure ℝ).real (S a)
  let g := fun N (i : Fin N) => spectralPartitionIndex S hcover (eig N i)
  have hc := spectral_label_counts_partition (fun k => k+1) Nat.succ_pos
    (fun k => eig (k+1)) ν hweak S hS hbd (fun k => g (k+1))
    (fun k a i => spectralPartitionIndex_eq_iff S hcover hdis (eig (k+1) i) a)
  have hp := positive_spectral_counts_tendsto (fun k => k+1) (fun k => g (k+1))
    w (fun _ => measureReal_nonneg) fallback hc
  have hfull : Tendsto (fun N a =>
      (spectralLabelCount (positiveSpectralLabel w fallback ∘ g N) a : ℝ)/N)
      atTop (𝓝 (fun a : {i // 0 < w i} => w a)) :=
    (tendsto_add_atTop_iff_nat 1).mp hp
  exact finite_type_pressure_tendsto hhaar hgauss hpub μ (fun a : {i // 0 < w i} => lam a)
    (fun N => positiveSpectralLabel w fallback ∘ g N) (fun a : {i // 0 < w i} => w a)
    (fun a => a.property) (positiveSpectralWeights_sum w (fun _ => measureReal_nonneg)
      (spectralPartitionWeights_sum (ν : Measure ℝ) S hcover hdis hS)) hfull aMax hMax

end InvariantIsing

end

end OAI
