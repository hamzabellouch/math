import OAI.Probability.InvariantIsing.Magnetic.RestrictedAncestorEndpoint
import OAI.Probability.InvariantIsing.Fields.MarkEndpointIntegral
import OAI.Probability.InvariantIsing.Fields.VectorPairIntegral
import OAI.Probability.InvariantIsing.Magnetic.RestrictedTerminalIntegrability
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldPublishedInput

namespace OAI

/-! The constrained vector terminal specialization of the joint marked-cascade theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma markPairEndpoint_coordinates {N n : ℕ} (g : ForestVertex n → Fin N → ℝ)
    (z : Fin N → ℝ) (α β : LabeledLeaf n) :
    markPairEndpoint n z z (fun i => (g (edgeAt n α i),g (edgeAt n β i))) =
      (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n g) α z,
        labeledEnergy n (markForestOfCoords (Fin N → ℝ) n g) β z) := by
  apply Prod.ext <;> funext j <;>
    simp only [markPairEndpoint,Pi.add_apply,Finset.sum_apply,labeledEnergy_edge_sum]

lemma restrictedFieldTiltedPairMean_eq_vector {N : ℕ} (S : Finset (Spin N))
    (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) :
    restrictedFieldTiltedPairMean S h z Φ =
    vectorTerminalPairMean N h.depth (chainExponent h.cut) (fieldStepVariance h)
      (restrictedFieldTerminal S) z
      (fun p => Φ (p.1,markPairEndpoint h.depth z z p.2)) := by
  unfold restrictedFieldTiltedPairMean vectorTerminalPairMean
  simp only [markPairEndpoint_coordinates]
  rfl

theorem panchenkoTalagrandRestrictedFieldPair_proved : PanchenkoTalagrandRestrictedFieldPairInput := by
  intro N hN S hS h z Φ hΦ hbounded
  obtain ⟨C,hB⟩ := hbounded
  let b := chainExponent h.cut
  let v := fieldStepVariance h
  have hb : CascadeExponents h.depth b := chainExponent_admissible h.ordered_cut h.first h.last
  let F := restrictedFieldTerminal S
  have hF : Measurable F := (continuous_restrictedFieldTerminal S hS).measurable
  have hG : HasLinearGrowth F := restrictedFieldTerminal_linearGrowth S hS
  have hD : Measurable (fun p : ℕ × (Fin h.depth → (Fin N → ℝ) × (Fin N → ℝ)) =>
      Φ (p.1,markPairEndpoint h.depth z z p.2)) :=
    hΦ.comp (measurable_fst.prodMk ((measurable_markPairEndpoint h.depth z z).comp measurable_snd))
  rw [restrictedFieldTiltedPairMean_eq_vector,
    vectorTerminal_pair_formula hN h.depth b v hb F hF hG z
      (restrictedTerminal_exp_integrable_ae hN S hS h z) _ hD (fun p => hB _)]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  let κ := vectorTerminalAncestorKernel N h.depth b v F hF
  let : ∀ i, IsMarkovKernel (κ i) := fun i =>
    vectorTerminalAncestorKernel_markov hN h.depth b v hb F hF hG i
  change markPairPathMean h.depth κ (fieldCommonLevel h α).val z z
    (fun w => Φ ((fieldCommonLevel h α).val,markPairEndpoint h.depth z z w)) = _
  calc
    _ = ∫ y, Φ ((fieldCommonLevel h α).val,y) ∂markPairEndpointKernel h.depth κ
        (fieldCommonLevel h α) z :=
      markPairPathMean_shared_endpoint h.depth κ (fieldCommonLevel h α) z
        (fun y => Φ ((fieldCommonLevel h α).val,y))
        (hΦ.comp (measurable_const.prodMk measurable_id)) (fun y => hB _)
    _ = _ := by
      rw [restrictedAncestor_pair hN S hS h.depth b v hb (fieldCommonLevel h α)]

end InvariantIsing

end

end OAI
