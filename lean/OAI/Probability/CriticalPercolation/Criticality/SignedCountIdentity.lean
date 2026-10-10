import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.ExpectedIncidenceTransport
import OAI.Probability.CriticalPercolation.Modular.SignedIncidenceTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma incidentClusterCount_toReal_le_two (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : (G.incidentClusterCount ω e).toReal≤2 := by
  exact (ENNReal.toReal_mono (by norm_num : (2:ℝ≥0∞)≠∞) (G.incidentClusterCount_le_two hc hl ω e)).trans_eq (by norm_num)

omit [Countable E] in
lemma measurable_centeredCoefficient (p : ℝ) (e : E) :
    Measurable (fun ω : Set E => centeredCoefficient p ω e) :=
  measurable_const.ite (measurable_set_mem e).setOf measurable_const

lemma integrable_incidentClusterCount_toReal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (e : E) : Integrable (fun ω => (G.incidentClusterCount ω e).toReal) (G.law p) := by
  apply Integrable.of_bound (G.measurable_incidentClusterCount e).ennreal_toReal.aestronglyMeasurable 2
  exact Eventually.of_forall (fun ω => by
    simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg] using G.incidentClusterCount_toReal_le_two hc hl ω e)

lemma integrable_centered_incidentClusterCount (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (e : E) :
    Integrable (fun ω => centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal) (G.law p) := by
  apply Integrable.of_bound ((measurable_centeredCoefficient p e).mul
    (G.measurable_incidentClusterCount e).ennreal_toReal).aestronglyMeasurable 2
  apply Eventually.of_forall
  intro ω
  change ‖centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal‖≤2
  rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (mul_le_mul (abs_centeredCoefficient_le_one p p.property ω e)
    (G.incidentClusterCount_toReal_le_two hc hl ω e) ENNReal.toReal_nonneg zero_le_one).trans_eq (one_mul 2)

lemma integrable_selectedIncidenceReturn_toReal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (H : Set E → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e)) (hH : ∀ ω e, H ω e≤1) (y : V) :
    Integrable (fun ω => (G.selectedIncidenceReturn hl H ω y).toReal) (G.law p) := by
  apply Integrable.of_bound
    (G.measurable_selectedIncidenceReturn hl H hm y).ennreal_toReal.aestronglyMeasurable ((hl y).toFinset.card*2)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num))
    (G.selectedIncidenceReturn_le hc hl H hH ω y)).trans_eq (by simp)

theorem expected_signed_discrepancy_count (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)=
      ∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
        ∫ ω, centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal ∂G.law p := by
  let A : Set E → E → ℝ≥0∞ := fun _ _ => 1
  let B : Set E → E → ℝ≥0∞ := fun ω e => if e∈ω then 1 else 0
  have hAm (e : E) : Measurable (fun ω => A ω e) := measurable_const
  have hBm (e : E) : Measurable (fun ω => B ω e) :=
    measurable_const.ite (measurable_set_mem e).setOf measurable_const
  have hA (ω : Set E) (e : E) : A ω e≤1 := le_rfl
  have hB (ω : Set E) (e : E) : B ω e≤1 := by dsimp [B]; split_ifs <;> simp
  have hAt := G.expected_selectedIncidence_real hc hl hq D K hD hK p A hAm hA (fun _ _ _ => rfl)
  have hBt := G.expected_selectedIncidence_real hc hl hq D K hD hK p B hBm hB (by
    intro φ ω e
    simp only [B,Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right])
  calc
    _ = (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.normalizedSelectedIncidence B ω x).toReal ∂G.law p) -
        (p:ℝ)*(∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.normalizedSelectedIncidence A ω x).toReal ∂G.law p) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [G.normalizedSignedDiscrepancy_eq_selected hc hl D K hD hK]
      rw [integral_sub (G.integrable_selectedIncidence_toReal hc hl D K hD hK p B hBm hB x)
        ((G.integrable_selectedIncidence_toReal hc hl D K hD hK p A hAm hA x).const_mul p),integral_const_mul]
    _ = _ := by
      rw [hBt,hAt,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      rw [←integral_const_mul,←integral_sub
        (G.integrable_selectedIncidenceReturn_toReal hc hl p B hBm hB y)
        ((G.integrable_selectedIncidenceReturn_toReal hc hl p A hAm hA y).const_mul p)]
      rw [←integral_finsetSum _ (fun e _ => G.integrable_centered_incidentClusterCount hc hl p e)]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω
      change (G.selectedIncidenceReturn hl B ω y).toReal -
        (p:ℝ)*(G.selectedIncidenceReturn hl A ω y).toReal =
        ∑ e∈(hl y).toFinset, centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal
      rw [G.selectedIncidenceReturn_toReal hc hl B hB,G.selectedIncidenceReturn_toReal hc hl A hA,
        Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e∈ω <;> simp [A,B,centeredCoefficient,he]; ring

end CriticalPercolation.BondGraph
end
end

end OAI
