import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteType
import OAI.Probability.InvariantIsing.Spectral.PositiveSpectralPartition

namespace OAI

/-! Null-boundary spectral rounding for the finite external-field formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical BigOperators Function
namespace InvariantIsing

theorem spectral_partition_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (hbd : ∀ i, (ν : Measure ℝ) (frontier (S i))=0)
    (lam : ι → ℝ) (fallback aMax : {i // 0 < (ν : Measure ℝ).real (S i)})
    (hMax : ∀ a : {i // 0 < (ν : Measure ℝ).real (S i)}, lam a ≤ lam aMax)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure
      (fun i => lam (positiveSpectralLabel (fun a => (ν : Measure ℝ).real (S a)) fallback
        (spectralPartitionIndex S hcover (eig N i))))
      (matrixRotation V⁻¹) (fun i => b (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR
        (finiteSpectralMeasure (fun i : {i // 0 < (ν : Measure ℝ).real (S i)} =>
          (ν : Measure ℝ).real (S i)) (fun i => lam i)) (lam aMax)) γ b).toReal) := by
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
  exact finite_type_field_pressure_tendsto hhaar hgauss hpub μ (fun a : {i // 0 < w i} => lam a)
    (fun N => positiveSpectralLabel w fallback ∘ g N) (fun a : {i // 0 < w i} => w a)
    (fun a => a.property) (positiveSpectralWeights_sum w (fun _ => measureReal_nonneg)
      (spectralPartitionWeights_sum (ν : Measure ℝ) S hcover hdis hS)) hfull aMax hMax group γ b hγ hγsum hgroup

end InvariantIsing

end

end OAI
