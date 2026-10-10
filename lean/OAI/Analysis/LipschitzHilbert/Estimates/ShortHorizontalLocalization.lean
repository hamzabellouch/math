import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeLpRealization
import OAI.Analysis.LipschitzHilbert.Estimates.L2Indicator

namespace OAI

/-! Finite horizontal propagation for the actual truncated operator.
An output set sees only its horizontal enlargement by the outer radius. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_horizontal_localization (K : ℝ → ℂ)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (S T : Set ℝ) (R : ℝ)
    (hK : ∀ t, R < |t| → K t=0) (hST : ∀ x∈S, ∀ t : ℝ, |t|≤R → x-t∈T) :
    (Prod.fst ⁻¹' S).indicator (shortSlopeOperator K u ((Prod.fst ⁻¹' T).indicator f))=
      (Prod.fst ⁻¹' S).indicator (shortSlopeOperator K u f) := by
  funext z
  by_cases hz : z.1∈S
  · rw [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz),
      Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)]
    unfold shortSlopeOperator
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : |t|≤R
    · have hin : (z.1-t,z.2-t*u z)∈Prod.fst ⁻¹' T := hST z.1 hz t ht
      rw [Set.indicator_of_mem hin]
    · rw [hK t (lt_of_not_ge ht)]
      simp only [zero_mul]
  · simp only [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hz)]

theorem shortL2Operator_horizontal_localization (K : ℝ → ℂ) (hKm : Measurable K) (hKi : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (S T : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (R : ℝ)
    (hK : ∀ t, R < |t| → K t=0) (hST : ∀ x∈S, ∀ t : ℝ, |t|≤R → x-t∈T)
    (f : Lp ℂ 2 planeMeasure) :
    l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
      (shortL2Operator K hKm hKi u hu
        (l2Indicator planeMeasure (Prod.fst ⁻¹' T) (hT.preimage measurable_fst) f))=
      l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
        (shortL2Operator K hKm hKi u hu f) := by
  let M := l2Indicator planeMeasure (Prod.fst ⁻¹' T) (hT.preimage measurable_fst)
  have hc := shortSlopeOperator_congr_ae K u hu (M f) ((Prod.fst ⁻¹' T).indicator f)
    (Lp.stronglyMeasurable (M f)).measurable
    ((Lp.stronglyMeasurable f).measurable.indicator (hT.preimage measurable_fst))
    (l2Indicator_coe planeMeasure _ _ f)
  apply Lp.ext
  filter_upwards [l2Indicator_coe planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
      (shortL2Operator K hKm hKi u hu (M f)),
    l2Indicator_coe planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
      (shortL2Operator K hKm hKi u hu f),
    shortL2Operator_coe K hKm hKi u hu (M f),hc,
    shortL2Operator_coe K hKm hKi u hu f] with z h1 h2 h3 h4 h5
  rw [h1,h2]
  by_cases hz : z.1∈S
  · simp only [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)]
    rw [h3,h4,h5]
    have hraw := congrFun (shortSlopeOperator_horizontal_localization K u f S T R hK hST) z
    simpa only [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)] using hraw
  · simp only [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hz)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
