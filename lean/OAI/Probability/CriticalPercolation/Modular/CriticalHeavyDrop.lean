import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Clusters.ForcedDisconnectContinuity
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyIdentity
import OAI.Probability.CriticalPercolation.Modular.SignedDiscrepancyContinuity

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma integrable_disconnectedIndicator (p : unitInterval) (e : E) :
    Integrable (fun ω => G.disconnectedIndicator ω e) (G.law p) :=
  Integrable.of_bound (G.measurable_disconnectedIndicator e).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω => G.norm_disconnectedIndicator_le ω e))

lemma integrable_clusterCountDrop (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (e : E) : Integrable (fun ω => G.clusterCountDrop ω e) (G.law p) := by
  apply Integrable.of_bound (G.measurable_clusterCountDrop e).aestronglyMeasurable 1
  apply Eventually.of_forall
  intro ω
  rcases G.clusterCountDrop_mem hc hl ω e with h|h <;> simp [h]

lemma tendsto_expected_signed_discrepancy_law (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) atTop
      (𝓝 (∑ x∈(G.orbitRepresentatives hq).roots,
        ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)) := by
  apply tendsto_finsetSum _
  intro x hx
  have h := G.tendsto_expected_normalizedSignedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx
  simpa only [G.integral_atParameter _ _ (G.measurable_normalizedSignedDiscrepancy _ x)] using h

theorem critical_expected_drop_eq_disconnected (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1) :
    (∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.clusterCountDrop ω e ∂G.law G.criticalProbability) =
    (∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law G.criticalProbability) := by
  obtain ⟨D,hD0,hD⟩ := G.uniform_incident_bound hq
  obtain ⟨K,hK⟩ := G.uniform_ball_bound hq 1
  obtain ⟨q,hmono,hqmem,hlim⟩ := exists_seq_strictMono_tendsto' hp0
  have hqp : ∀ n, q n≤G.criticalProbability := fun n => (hqmem n).2.le
  have hsig := G.tendsto_expected_signed_discrepancy_law hc hl hq D K hD hK
    G.criticalProbability q hmono.monotone hqp hlim
  have hd : Tendsto (fun n => ∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law (q n)) atTop
      (𝓝 (∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law G.criticalProbability)) := by
    apply tendsto_finsetSum _
    intro y hy
    apply tendsto_finsetSum _
    intro e he
    exact G.tendsto_integral_disconnectedIndicator G.criticalProbability q hmono.monotone hqp hlim e
  have hqreal : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 (G.criticalProbability:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  have hprod := ((hqreal.neg.mul (hqreal.const_sub 1)).mul hd)
  have heq (n : ℕ) : (∑ x∈(G.orbitRepresentatives hq).roots,
      ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) =
      -(q n:ℝ)*(1-(q n:ℝ))*(∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law (q n)) := by
    rw [G.expected_signed_discrepancy_drop hc hl hq D K hD hK]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro e he
    exact integral_congr_ae (G.clusterCountDrop_eq_disconnected_ae_subcritical hc hl (q n) (hqmem n).2 e)
  have hv := tendsto_nhds_unique hsig (hprod.congr' (Eventually.of_forall (fun n => (heq n).symm)))
  rw [G.expected_signed_discrepancy_drop hc hl hq D K hD hK] at hv
  apply mul_left_cancel₀ (a := -(G.criticalProbability:ℝ)*(1-(G.criticalProbability:ℝ))) _ hv
  exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt (show 0<(G.criticalProbability:ℝ) from hp0)))
    (sub_ne_zero.mpr (ne_of_gt (show (G.criticalProbability:ℝ)<1 from hp1)))

theorem critical_root_incident_drop_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1)
    (y : V) (hy : y∈(G.orbitRepresentatives hq).roots) (e : E) (he : y∈G.ends e) :
    (fun ω => G.disconnectedIndicator ω e)=ᵐ[G.law G.criticalProbability]
      (fun ω => G.clusterCountDrop ω e) := by
  let f := fun (e : E) ω => G.disconnectedIndicator ω e-G.clusterCountDrop ω e
  have hnon (e : E) (ω : Set E) : 0≤f e ω := sub_nonneg.mpr (G.clusterCountDrop_le_disconnected hc hl ω e)
  have hint (e : E) : Integrable (f e) (G.law G.criticalProbability) :=
    (G.integrable_disconnectedIndicator _ e).sub (G.integrable_clusterCountDrop hc hl _ e)
  have hsum : (∑ z∈(G.orbitRepresentatives hq).roots, ∑ a∈(hl z).toFinset,
      ∫ ω, f a ω ∂G.law G.criticalProbability)=0 := by
    simp_rw [f,integral_sub (G.integrable_disconnectedIndicator _ _)
      (G.integrable_clusterCountDrop hc hl _ _),Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (G.critical_expected_drop_eq_disconnected hc hl hq hp0 hp1).symm
  have hout : (∑ a∈(hl y).toFinset, ∫ ω, f a ω ∂G.law G.criticalProbability)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun z hz => Finset.sum_nonneg
      (fun a ha => integral_nonneg (hnon a)))).mp hsum y hy
  have hin : (∫ ω, f e ω ∂G.law G.criticalProbability)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => integral_nonneg (hnon a))).mp hout e
      ((hl y).mem_toFinset.mpr he)
  have hae := (integral_eq_zero_iff_of_nonneg (hnon e) (hint e)).mp hin
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp hω

end CriticalPercolation.BondGraph
end
end

end OAI
