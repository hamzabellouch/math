import OAI.Probability.InvariantIsing.Magnetic.MagneticZeroPopulationLimit
import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteLawExtension
import OAI.Probability.InvariantIsing.Fields.FieldQuantizer

namespace OAI

/-! Pressure convergence for each finite null-boundary quantization of the field. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Classical BigOperators
namespace InvariantIsing

theorem quantized_mean_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (P : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (P N)]
    [∀ N, (P N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1))) atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (hfield : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) atTop (𝓝 ξ))
    {n : ℕ} (c r : Fin n → ℝ)
    (hnull : ∀ i, (ξ : Measure ℝ) (frontier (ball (c i) (r i)))=0) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹)
      (fun i => fieldBallSimple c r (field N i)) ∂P N) atTop
      (𝓝 (simpleFieldValue (ξ : Measure ℝ) (fieldBallSimple c r) (measureR (ν : Measure ℝ) b))) := by
  let S := spectralBallCell (fun i => ball (c i) (r i))
  let γ := fun i => (ξ : Measure ℝ).real (S i)
  let val := fun i : Option (Fin n) => i.elim 0 c
  let g := fun N (i : Fin N) => spectralPartitionIndex S (spectralBallCell_cover _) (field N i)
  have hS : ∀ i, MeasurableSet (S i) := spectralBallCell_measurable _ (fun _ => measurableSet_ball)
  have hγsum : ∑ i, γ i=1 := spectralPartitionWeights_sum (ξ : Measure ℝ) S
    (spectralBallCell_cover _) (spectralBallCell_disjoint _) hS
  obtain ⟨j,hj⟩ := exists_pos_spectral_weight (fun _ => measureReal_nonneg) hγsum
  let fallback : {i // 0 < γ i} := ⟨j,hj⟩
  have hg1 := spectral_label_counts_partition (fun k => k+1) Nat.succ_pos
    (fun k => field (k+1)) ξ hfield S hS (spectralBallCell_null_boundary _ _ hnull)
    (fun k => g (k+1)) (fun k i j => spectralPartitionIndex_eq_iff S (spectralBallCell_cover _)
      (spectralBallCell_disjoint _) (field (k+1) j) i)
  have hg : Tendsto (fun N i => (spinGroupSize (g N) i : ℝ)/N) atTop (𝓝 γ) := by
    have hh : Tendsto (fun N i => (spectralLabelCount (g N) i : ℝ)/N) atTop (𝓝 γ) :=
      (tendsto_add_atTop_iff_nat 1).mp hg1
    simpa only [spectralLabelCount_eq_spinGroupSize] using hh
  have hp := general_spectral_mean_field_positive_part_tendsto hhaar hgauss hpub P eig ν a b
    hcompact hbound ha hb hno hweak g γ val (fun _ => measureReal_nonneg) hγsum fallback hg
  have he : (ξ : Measure ℝ).map (fieldBallSimple c r)=
      finiteSpectralMeasure (fun i : {i // 0 < γ i} => γ i) (fun i => val i) := by
    rw [finiteSpectralMeasure_positive γ val (fun _ => measureReal_nonneg)]
    exact spectralPartition_pushforward (ξ : Measure ℝ) S (spectralBallCell_cover _)
      (spectralBallCell_disjoint _) hS val
  have hv := simpleFieldValue_eq_finite_law ν a b hcompact hbound ha hb
    (ξ : Measure ℝ) (fieldBallSimple c r) (fun i : {i // 0 < γ i} => γ i) (fun i => val i)
    (fun i => i.property) (positiveSpectralWeights_sum γ (fun _ => measureReal_nonneg) hγsum) he
  rw [hv]
  exact hp

end InvariantIsing

end

end OAI
