import OAI.Probability.InvariantIsing.Spectral.CompactPartitionPressure
import OAI.Probability.InvariantIsing.Magnetic.MagneticSpectralPartition

namespace OAI

/-! Positive spectral partition bounds for the finite-field pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function
namespace InvariantIsing.CompactSpectralPartition
variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

lemma field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => D.lowerValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR (D.law : Measure ℝ) D.edge) γ c).toReal) ∧
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => D.upperValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR (D.law : Measure ℝ) D.edge) γ c).toReal) := by
  have hh (fallback : D.Positive) := spectral_partition_field_pressure_tendsto hhaar hgauss hpub μ eig ν hweak
    D.cells (spectralBallCell_cover _) (spectralBallCell_disjoint _)
    (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
    (spectralBallCell_null_boundary (ν : Measure ℝ) _ D.null_boundary)
    D.value fallback D.upper D.le_upper group γ c hγ hγsum hgroup
  exact ⟨hh D.lower,hh D.upper⟩

lemma mean_field_pressure_bounds {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig : Fin N → ℝ)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hab : a ≤ b) (heig : ∀ i, eig i∈Icc a b) (c : Fin N → ℝ) :
    (∫ V, rotatedPressure (fun i => D.lowerValue (eig i))
      (matrixRotation V⁻¹) c ∂μ)-δ/2 ≤
        ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ ∧
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ) ≤
      (∫ V, rotatedPressure (fun i => D.upperValue (eig i))
        (matrixRotation V⁻¹) c ∂μ)+δ/2 := by
  let K := max |a| |b|
  have hbound (x : ℝ) (hx : x∈Icc a b) : |x| ≤ K := by
    apply abs_le.mpr
    constructor
    · have hh := neg_abs_le a
      have hk : |a| ≤ K := le_max_left _ _
      linarith [hx.1]
    · exact hx.2.trans ((le_abs_self b).trans (le_max_right _ _))
  exact cavity_meanPressure_squeeze hN μ eig (fun i => D.lowerValue (eig i))
    (fun i => D.upperValue (eig i)) c δ K
    (fun i => hbound _ (heig i))
    (fun i => hbound _ (D.rounded_mem hab (eig i)).1)
    (fun i => hbound _ (D.rounded_mem hab (eig i)).2)
    (fun i => (D.rounding_bounds ha hb _ (heig i)).1)
    (fun i => (D.rounding_bounds ha hb _ (heig i)).2)

end InvariantIsing.CompactSpectralPartition

end

end OAI
