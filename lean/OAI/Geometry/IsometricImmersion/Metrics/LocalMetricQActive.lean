import OAI.Geometry.IsometricImmersion.Metrics.MetricQSpatialBundle
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem metricQSpatialBundle_mapsTo_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (theta : ℝ) :
    MapsTo (metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) universalMetricQDomain := by
  intro v hv
  exact ⟨metricDet_ne_zero hg hv.1,
    by simpa only [metricQSpatialBundle, Function.comp_apply, universalQDenominator_metricPBundle] using hv.2⟩

theorem actual_fixedTime_Q_jet_bound_from_universalTube
    {g : MetricField} {U : Set Coord} {theta : ℝ} {v : QSpatialState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hv : v ∈ qFixedTimeDomain g U theta)
    {N : ℕ} {G W d c C : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    (hwB : ‖qFixedTimeState theta v‖ ≤ W)
    (hdet : d ≤ |(g (coordinatePoint (v 0) theta)).det|)
    (hden : c ≤ |stateQDenominator g (qFixedTimeState theta v)|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricQTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (qFixedTimeQ g theta) v‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := qFixedTimeDomain_isOpen hg hU theta
  have hsub : qFixedTimeDomain g U theta ⊆ qFixedTimeBaseDomain U theta := by
    intro w hw
    simpa only [statePoint_qFixedTimeState, qFixedTimeBaseDomain, Set.mem_ofPred_eq] using hw.1
  have hf := (metricQSpatialBundle_contDiffOn hg hU theta).mono hsub
  have hmap := metricQSpatialBundle_mapsTo_domain hg theta
  have hmem : metricQSpatialBundle g theta v ∈ universalMetricQTube (max G W) d c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using metricQSpatialBundle_norm_bound hG hgB hwB
    · simpa only [metricQSpatialBundle, Function.comp_apply, metricPBundle, statePoint_qFixedTimeState,
        Set.mem_preimage, Set.mem_Ici] using hdet
    · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, metricQSpatialBundle,
        Function.comp_apply, universalQDenominator_metricPBundle] using hden
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricQ universalMetricQDomain (metricQSpatialBundle g theta v)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricQDomain_isOpen
      (universalMetricQTube_subset_domain (max G W) hd hc hmem)]
    exact hC i (hi.trans hn) _ hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) v‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hv]
    exact (metricQSpatialBundle_positive_jet_bound hg hU (hsub hv) hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricQ_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hv ho hi
  have heq : iteratedFDerivWithin ℝ n (qFixedTimeQ g theta) (qFixedTimeDomain g U theta) v =
      iteratedFDerivWithin ℝ n (universalMetricQ ∘ metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) v :=
    iteratedFDerivWithin_congr
      (fun w hw => sixVariableQ_eq_universalMetricQ hg hU hw.1) hv n
  rw [iteratedFDerivWithin_of_isOpen n hD hv] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_fixedTime_Q_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ (theta : ℝ) (v : QSpatialState),
      coordinatePoint (v 0) theta ∈ U →
      HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G →
      ‖qFixedTimeState theta v‖ ≤ W →
      d ≤ |(g (coordinatePoint (v 0) theta)).det| →
      c ≤ |stateQDenominator g (qFixedTimeState theta v)| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (qFixedTimeQ g theta) v‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCQ⟩ := universalMetricQTube_finite_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU theta v hp hgB hwB hdet hden n hn
  have hne : stateQDenominator g (qFixedTimeState theta v) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hv : v ∈ qFixedTimeDomain g U theta :=
    ⟨by simpa only [statePoint_qFixedTimeState] using hp, hne⟩
  have hb := actual_fixedTime_Q_jet_bound_from_universalTube hg hU hv hG hd hc hgB hwB hdet hden hCQ hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun i _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

theorem qSolutionJet_norm_bound_of_coordinateBound
    {z : Coord → ℝ} {S : Set Coord} {R Z : ℝ} (hR : 0 ≤ R)
    (hzB : CoordinateBound z S 2 Z)
    (hcoords : ∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) {p : Coord} (hp : p ∈ S) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (hcoords p hp).1.trans (le_max_left _ _)
  · exact (hcoords p hp).2.trans (le_max_left _ _)
  · exact (hzB [0] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0] (by norm_num) p hp).trans (le_max_right _ _)

theorem exists_same_region_active_Q_coefficient_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ p ∈ S,
        |qCoordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hQ⟩ := exists_local_fixedTime_Q_jet_bound G (max R Z) hG hd hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hcoords hgB hzB hdet hden w hw r hactive p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hpoint : coordinatePoint (qSpatialProjection (qSolutionJet z p) 0) (p 1) = p := point_eta p
  have hbound := hQ g U hg hU (p 1) (qSpatialProjection (qSolutionJet z p))
    (by simpa only [hpoint] using hSU hp)
    (by simpa only [hpoint] using hgB p hp)
    (by rw [he]; exact qSolutionJet_norm_bound_of_coordinateBound hR hzB hcoords hp)
    (by simpa only [hpoint] using hdet p hp)
    (by rw [he, stateQDenominator_qSolutionJet]; exact hden p hp)
    w.arity (q_residual_factor_orders hw r).2
  exact (qCoordinateChainCoefficient_abs_le_fixedTime_derivative hg hU (hSU hp) hxx w r hactive).trans hbound

end SmoothLocal.HighEquation

end

end OAI
