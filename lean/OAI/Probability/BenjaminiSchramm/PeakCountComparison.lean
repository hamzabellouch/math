import OAI.Probability.BenjaminiSchramm.PeakExposureComparison
import OAI.Probability.BenjaminiSchramm.SlabSecondMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma lintegral_indicator_restrictedLayerCount (p : unitInterval)
    (P : Set (Set E)) (hP : MeasurableSet P) (I : Set E) (W : Set V) (x : V) :
    (∫⁻ ω, P.indicator (fun ω => restrictedLayerCount G I W ω x) ω ∂law p) =
      ∑' w, if w ∈ W then law p (P ∩ {ω | Conn G (ω ∩ I) x w}) else 0 := by
  have hm (w : V) : MeasurableSet (P ∩ {ω | Conn G (ω ∩ I) x w}) := by
    have hi : Measurable (fun ω : Set E => ω ∩ I) :=
      measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
    exact hP.inter ((measurableSet_conn G x w).preimage hi)
  have he (ω : Set E) : P.indicator (fun ω => restrictedLayerCount G I W ω x) ω =
      ∑' w, if w ∈ W then (P ∩ {ω | Conn G (ω ∩ I) x w}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω else 0 := by
    by_cases hp : ω ∈ P
    · rw [Set.indicator_of_mem hp]
      unfold restrictedLayerCount
      apply tsum_congr
      intro w
      by_cases hw : w ∈ W <;> by_cases hc : Conn G (ω ∩ I) x w <;>
        simp only [hw,hc,hp,Set.indicator,Set.mem_inter_iff,Set.mem_ofPred_eq,
          and_true,and_false,ite_true,ite_false]
    · rw [Set.indicator_of_notMem hp]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro w
      by_cases hw : w ∈ W <;>
        simp only [hw,hp,Set.indicator,Set.mem_inter_iff,false_and,ite_true,ite_false]
  simp_rw [he]
  rw [lintegral_tsum (fun w => (by
    by_cases hw : w ∈ W
    · simpa only [hw,ite_true] using ((measurable_const.indicator (hm w)).aemeasurable)
    · simp only [hw,ite_false]
      exact aemeasurable_const))]
  apply tsum_congr
  intro w
  by_cases hw : w ∈ W
  · simp only [hw,ite_true]
    exact lintegral_indicator_one (hm w)
  · simp only [hw,ite_false,lintegral_zero]

theorem upper_cluster_peak_layer_comparison_in_domain (p : unitInterval)
    (D D' K J : Set E) (hKD : K ⊆ D) (hKD' : K ⊆ D') (hJD' : J ⊆ D') (x u : V) (A T W : Set V)
    (hu : u ∈ A) (hAT : Disjoint A T)
    (hJI : J ⊆ D \ (K ∩ ballIncidentEdges G A))
    (hfin : ∀ᵐ ω ∂law p,
      (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u).Finite) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) *
      (∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0) ≤
    ∫⁻ ω, ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ).indicator
      (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := by
  rw [lintegral_indicator_restrictedLayerCount G p _
    ((measurableSet_restricted_exactCluster G K x A).inter
      (measurableSet_restrictedHit G D x T).compl),←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w ∈ W
  · simp only [hw,ite_true]
    exact upper_cluster_peak_connection_comparison_in_domain G p D D' K J hKD hKD' hJD' x u w A T hu hAT hJI hfin
  · simp only [hw,ite_false,mul_zero]
    exact le_rfl

theorem upper_cluster_peak_layer_comparison (p : unitInterval)
    (D K J : Set E) (hKD : K ⊆ D) (x u : V) (A T W : Set V)
    (hu : u ∈ A) (hAT : Disjoint A T)
    (hJI : J ⊆ D \ (K ∩ ballIncidentEdges G A))
    (hfin : ∀ᵐ ω ∂law p,
      (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u).Finite) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) *
      (∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0) ≤
    ∫⁻ ω, ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ).indicator
      (fun ω => restrictedLayerCount G D W ω x) ω ∂law p :=
  upper_cluster_peak_layer_comparison_in_domain G p D D K J hKD hKD
    (hJI.trans Set.sdiff_subset) x u A T W hu hAT hJI hfin

end Percolation.BenjaminiSchramm

end

end OAI
