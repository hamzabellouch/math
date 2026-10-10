import OAI.Probability.InvariantIsing.Spectral.SelectedTypePressure
import OAI.Probability.InvariantIsing.Spectral.CompactPartitionPressure

namespace OAI

/-! Spectral rounding for a sequence of selected dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function
namespace InvariantIsing

theorem selected_partition_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (eig : (k : ℕ) → Fin (D k) → ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hD k) (eig k)) atTop (𝓝 ν))
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (hbd : ∀ i, (ν : Measure ℝ) (frontier (S i))=0)
    (lam : ι → ℝ) (fallback aMax : {i // 0 < (ν : Measure ℝ).real (S i)})
    (hMax : ∀ a : {i // 0 < (ν : Measure ℝ).real (S i)}, lam a ≤ lam aMax) :
    Tendsto (fun k => ∫ V, rotatedPressure
      (fun i => lam (positiveSpectralLabel (fun a => (ν : Measure ℝ).real (S a)) fallback
        (spectralPartitionIndex S hcover (eig k i))))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR
        (finiteSpectralMeasure (fun i : {i // 0 < (ν : Measure ℝ).real (S i)} =>
          (ν : Measure ℝ).real (S i)) (fun i => lam i)) (lam aMax))).toReal) := by
  let w := fun a => (ν : Measure ℝ).real (S a)
  let g := fun k (i : Fin (D k)) => spectralPartitionIndex S hcover (eig k i)
  have hc := spectral_label_counts_partition D hD eig ν hweak S hS hbd g
    (fun k a i => spectralPartitionIndex_eq_iff S hcover hdis (eig k i) a)
  have hp := positive_spectral_counts_tendsto D g w (fun _ => measureReal_nonneg) fallback hc
  exact selected_finite_type_pressure_tendsto hhaar hgauss hpub μ
    (fun a : {i // 0 < w i} => lam a) D hD hDlim
    (fun k => positiveSpectralLabel w fallback ∘ g k) (fun a : {i // 0 < w i} => w a)
    (fun a => a.property) (positiveSpectralWeights_sum w (fun _ => measureReal_nonneg)
      (spectralPartitionWeights_sum (ν : Measure ℝ) S hcover hdis hS)) hp aMax hMax

namespace CompactSpectralPartition

lemma selected_pressure_tendsto {ν : ProbabilityMeasure ℝ} {a b δ : ℝ}
    (P : CompactSpectralPartition ν a b δ)
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (eig : (k : ℕ) → Fin (D k) → ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hD k) (eig k)) atTop (𝓝 ν)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.lowerValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) ∧
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.upperValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) := by
  have hh (fallback : P.Positive) := selected_partition_pressure_tendsto hhaar hgauss hpub μ
    D hD hDlim eig ν hweak P.cells (spectralBallCell_cover _) (spectralBallCell_disjoint _)
    (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
    (spectralBallCell_null_boundary (ν : Measure ℝ) _ P.null_boundary)
    P.value fallback P.upper P.le_upper
  exact ⟨hh P.lower,hh P.upper⟩

end CompactSpectralPartition
end InvariantIsing

end

end OAI
