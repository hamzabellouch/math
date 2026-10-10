import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldPairInput
import OAI.Probability.InvariantIsing.Core.UnrestrictedEndpointKernel
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldRootLoss

namespace OAI

/-! The ordinary vector log-cosh specialization of the proved joint marking law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators
namespace InvariantIsing

lemma restrictedFieldTiltedPairMean_univ (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) :
    restrictedFieldTiltedPairMean (Finset.univ : Finset (Spin N)) h z Φ =
      fieldVectorTiltedPairMean N h z Φ := by
  unfold restrictedFieldTiltedPairMean fieldVectorTiltedPairMean
  simp only [restrictedFieldTerminal_univ]

theorem panchenkoTalagrandFieldPair_proved : PanchenkoTalagrandFieldPairInput := by
  intro N hN h z Φ hΦ hB
  rw [← restrictedFieldTiltedPairMean_univ]
  rw [panchenkoTalagrandRestrictedFieldPair_proved N hN Finset.univ Finset.univ_nonempty h z Φ hΦ hB]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  have he := restrictedPairEndpointKernel_univ hN h.depth (chainExponent h.cut)
    (fieldStepVariance h) (fun i hi => (hb.1 i hi).1) (fieldCommonLevel h α)
  have ht := fieldVectorPairEndpointKernel_transport N (fieldStepIncrements h)
    (finiteFieldIncrements_positive h.depth (chainExponent h.cut) (fieldStepVariance h)
      (fun i hi => (hb.1 i hi).1)) (scalarFieldIncrements_positive h)
    (Fin.cast (by simp) (fieldCommonLevel h α))
    (Fin.cast (by rw [scalarFieldIncrements_length]) (fieldCommonLevel h α)) rfl
  dsimp only
  rw [he,ht]

end InvariantIsing

end

end OAI
