import OAI.Geometry.IsometricImmersion.Metrics.UniversalMetricQ
import OAI.Geometry.IsometricImmersion.Metrics.LocalMetricPCoefficients

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem metricPBundle_mapsTo_Q_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    MapsTo (metricPBundle g) (darbouxQStateDomain g U) universalMetricQDomain := by
  intro w hw
  exact ⟨metricDet_ne_zero hg hw.1,
    by simpa only [universalQDenominator_metricPBundle] using hw.2⟩

theorem metricPBundle_mem_universalQTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d c : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateQDenominator g w|) :
    metricPBundle g w ∈ universalMetricQTube (max G W) d c := by
  refine ⟨⟨?_, hdet⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      metricPBundle_norm_bound hg hU hw hG hgB hwB
  · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, universalQDenominator_metricPBundle] using hden

theorem actualQ_jet_bound_from_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) {N : ℕ} {G W d c C : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateQDenominator g w|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricQTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := darbouxQStateDomain_isOpen hg hU
  have hsub : darbouxQStateDomain g U ⊆ stateBaseDomain U := fun _ hv => hv.1
  have hf := (metricPBundle_contDiffOn hg hU).mono hsub
  have hmap := metricPBundle_mapsTo_Q_domain hg
  have hmem := metricPBundle_mem_universalQTube hg hU hw.1 hG
    (fun i j k hk => hgB i j k (by omega)) hwB hdet hden
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricQ universalMetricQDomain (metricPBundle g w)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricQDomain_isOpen
      (universalMetricQTube_subset_domain (max G W) hd hc hmem)]
    exact hC i (hi.trans hn) (metricPBundle g w) hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricPBundle g) (darbouxQStateDomain g U) w‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hw]
    exact (metricPBundle_positive_jet_bound hg hU hw.1 hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricQ_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hw ho hi
  have heq : iteratedFDerivWithin ℝ n (sixVariableQ g) (darbouxQStateDomain g U) w =
      iteratedFDerivWithin ℝ n (universalMetricQ ∘ metricPBundle g) (darbouxQStateDomain g U) w :=
    iteratedFDerivWithin_congr (fun _ hv => sixVariableQ_eq_universalMetricQ hg hU hv.1) hw n
  rw [iteratedFDerivWithin_of_isOpen n hD hw] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_metric_Q_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ w : DarbouxState,
      statePoint w ∈ U →
      (∀ i j k, k ≤ N + 2 →
        ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → d ≤ |(g (statePoint w)).det| → c ≤ |stateQDenominator g w| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCP⟩ := universalMetricQTube_finite_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU w hw hgB hwB hdet hden n hn
  have hne : stateQDenominator g w ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hb := actualQ_jet_bound_from_universalTube hg hU ⟨hw, hne⟩ hG hd hc hgB hwB hdet hden hCP hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

end SmoothLocal.HighEquation

end

end OAI
