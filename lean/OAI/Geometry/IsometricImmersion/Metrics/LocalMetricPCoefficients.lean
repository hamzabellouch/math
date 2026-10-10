import OAI.Geometry.IsometricImmersion.Metrics.MetricPBundleBounds
import OAI.Geometry.IsometricImmersion.Metrics.RemainderCoefficientBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem metricPBundle_norm_bound {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) : ‖metricPBundle g w‖ ≤ max G W := by
  have hb0 (i j : Fin 2) : |g (statePoint w) i j| ≤ G := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
  have hb1 (d i j : Fin 2) : |coordPartial d (fun p => g p i j) (statePoint w)| ≤ G := by
    have hh := (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw d 0).trans
      (hgB i j 1 (by omega))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have hb2 (d e i j : Fin 2) :
      |coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)| ≤ G := by
    have hh := ((norm_iteratedFDeriv_coordPartial_le
      (partial_contDiffOn (hg.1 i j) hU e) hU hw d 0).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw e 1)).trans (hgB i j 2 (by omega))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have h0 : ‖g (statePoint w)‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb0 i j))
  have h1 : ‖(fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb1 d i j)))
  have h2 : ‖(fun d e i j =>
      coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun e =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
          (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb2 d e i j))))
  change max ‖g (statePoint w)‖
    (max ‖(fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖
      (max ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖
        ‖w‖)) ≤ max G W
  exact max_le (h0.trans (le_max_left _ _))
    (max_le (h1.trans (le_max_left _ _))
      (max_le (h2.trans (le_max_left _ _)) (hwB.trans (le_max_right _ _))))

theorem metricPBundle_mapsTo_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    MapsTo (metricPBundle g) (darbouxStateDomain g U) universalMetricDomain := by
  intro w hw
  exact ⟨metricDet_ne_zero hg hw.1,
    by simpa only [universalDenominator_metricPBundle] using hw.2⟩

theorem metricPBundle_mem_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d c : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateDenominator g w|) :
    metricPBundle g w ∈ universalMetricTube (max G W) d c := by
  refine ⟨⟨?_, hdet⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      metricPBundle_norm_bound hg hU hw hG hgB hwB
  · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, universalDenominator_metricPBundle] using hden

theorem actualP_jet_bound_from_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxStateDomain g U) {N : ℕ} {G W d c C : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateDenominator g w|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricP a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (sixVariableP g) w‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := darbouxStateDomain_isOpen hg hU
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun _ hv => hv.1
  have hf := (metricPBundle_contDiffOn hg hU).mono hsub
  have hmap := metricPBundle_mapsTo_domain hg
  have hmem := metricPBundle_mem_universalTube hg hU hw.1 hG
    (fun i j k hk => hgB i j k (by omega)) hwB hdet hden
  have hdomain := universalMetricTube_subset_domain (max G W) hd hc hmem
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricP universalMetricDomain (metricPBundle g w)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricDomain_isOpen hdomain]
    exact hC i (hi.trans hn) (metricPBundle g w) hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricPBundle g) (darbouxStateDomain g U) w‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hw]
    exact (metricPBundle_positive_jet_bound hg hU hw.1 hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricP_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hw ho hi
  have heq : iteratedFDerivWithin ℝ n (sixVariableP g) (darbouxStateDomain g U) w =
      iteratedFDerivWithin ℝ n (universalMetricP ∘ metricPBundle g) (darbouxStateDomain g U) w :=
    iteratedFDerivWithin_congr (fun _ hv => sixVariableP_eq_universalMetricP hg hU hv.1) hw n
  rw [iteratedFDerivWithin_of_isOpen n hD hw] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_metric_P_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ w : DarbouxState,
      statePoint w ∈ U →
      (∀ i j k, k ≤ N + 2 →
        ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → d ≤ |(g (statePoint w)).det| → c ≤ |stateDenominator g w| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (sixVariableP g) w‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCP⟩ := universalMetricTube_finite_P_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun index _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU w hw hgB hwB hdet hden n hn
  have hne : stateDenominator g w ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hb := actualP_jet_bound_from_universalTube hg hU ⟨hw, hne⟩ hG hd hc hgB hwB hdet hden hCP hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun index _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

theorem exists_same_region_solution_P_jet_bound (G Z : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U → S ⊆ modelSquare →
      (∀ i j k, k ≤ N + 2 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 1 1|) →
      ∀ n ≤ N, ∀ p ∈ S, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C := by
  obtain ⟨C, hC, hP⟩ := exists_local_metric_P_jet_bound G (max 3 Z) hG hd hc N
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hSS hgB hzB hdet hden n hn p hp
  have hwB : ‖solutionJet z p‖ ≤ max 3 Z := by
    apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_left _ _))).mpr
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact (abs_le.mpr ⟨(hSS hp).1 0, (hSS hp).2 0⟩).trans (le_max_left 3 Z)
    · exact (abs_le.mpr ⟨(hSS hp).1 1, (hSS hp).2 1⟩).trans (le_max_left 3 Z)
    · exact (hzB [0] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [1] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [1, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
  exact hP g U hg hU (solutionJet z p)
    (by simpa only [statePoint_solutionJet] using hSU hp)
    (fun i j k hk => by simpa only [statePoint_solutionJet] using hgB i j k hk p hp)
    hwB (by simpa only [statePoint_solutionJet] using hdet p hp)
    (by simpa only [stateDenominator_solutionJet] using hden p hp) n hn

theorem exists_same_region_remainder_outer_bound (G Z : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U → S ⊆ modelSquare →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 1 1|) →
      ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ S,
        |coordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hP⟩ := exists_same_region_solution_P_jet_bound G Z hG hd hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hSS hgB hzB hdet hden w hw r p hp
  exact (coordinateChainCoefficient_abs_le_full_derivative g z w r p).trans
    (hP g z U S hg hU hSU hSS (fun i j k hk => hgB i j k (by omega)) hzB hdet hden
      w.arity (residual_scalar_factor_orders hw r).2 p hp)

end SmoothLocal.HighEquation

end

end OAI
