import OAI.Geometry.IsometricImmersion.Metrics.LocalMetricQActive

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qSpatialProjection_norm_le (w : DarbouxState) : ‖qSpatialProjection w‖ ≤ ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm w 0
  · exact norm_le_pi_norm w 2
  · exact norm_le_pi_norm w 3
  · exact norm_le_pi_norm w 4
  · exact norm_le_pi_norm w 5

theorem qSpatialCLM_projection_of_time_zero {w : DarbouxState} (hw : w 1 = 0) :
    qSpatialCLM (qSpatialProjection w) = w := by
  have he := qFixedTimeState_projection w
  simpa only [qFixedTimeState, hw, Pi.single_zero, add_zero] using he

theorem coordPartial_qSolutionJet_xi_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) :
    ‖coordPartial 0 (qSolutionJet z) p‖ ≤ max 1 Z := by
  have he := coordinate_qSolutionJet_horizontal_positive hU hz (hSU hp) 1 (by norm_num)
  change coordPartial 0 (qSolutionJet z) p = _ at he
  rw [he]
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp
  · simp
  · exact (hzB [0, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

theorem heightQCoefficient_xi_eq_fixedTime_second
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) (i : Fin 6) (hi : i ≠ 1) :
    coordPartial 0 (heightQCoefficient g z i) p =
      iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))
        ![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) 1] := by
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hv : qSpatialProjection (qSolutionJet z p) ∈ qFixedTimeDomain g U (p 1) := by
    change qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) ∈ darbouxQStateDomain g U
    rw [he]
    exact qSolutionJet_mem_domain hp hxx
  have htime : coordPartial 0 (qSolutionJet z) p 1 = 0 := by
    have hh := congrArg (fun v : DarbouxState => v 1)
      (coordinate_qSolutionJet_horizontal_positive hU hz hp 1 (by norm_num))
    exact hh
  rw [qFixedTimeQ_iteratedFDeriv hg hU hv 2,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
  have hvec : (fun j : Fin 2 => qSpatialCLM
      (![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) 1] j)) =
      ![coordPartial 0 (qSolutionJet z) p, Pi.single i 1] := by
    funext j
    fin_cases j
    · exact qSpatialCLM_projection_of_time_zero htime
    · change qSpatialCLM (Pi.single (qSpatialIndex i) 1) = Pi.single i 1
      rw [qSpatialCLM_single, qSpatialAxis_index hi]
  rw [hvec]
  exact (second_fderiv_comp_constant_direction_xi
    (sixVariableQ_contDiffAt_solutionJet hg hU hp hxx)
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (Pi.single i 1)).symm

theorem heightQCoefficient_xi_bound_of_fixedTime_second
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord} {Z C : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : S ⊆ U) (hzB : CoordinateBound z S 3 Z) (hC : 0 ≤ C)
    {p : Coord} (hp : p ∈ S) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : ‖iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))‖ ≤ C)
    (i : Fin 6) (hi : i ≠ 1) :
    |coordPartial 0 (heightQCoefficient g z i) p| ≤ C * max 1 Z := by
  rw [heightQCoefficient_xi_eq_fixedTime_second hg hU hz (hSU hp) hxx i hi, ← Real.norm_eq_abs]
  have hd := (qSpatialProjection_norm_le (coordPartial 0 (qSolutionJet z) p)).trans
    (coordPartial_qSolutionJet_xi_norm_bound hU hz hSU hzB hp)
  have hb := (iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1))
    (qSpatialProjection (qSolutionJet z p))).le_opNorm
      ![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) (1 : ℝ)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (mul_le_mul hQ hd (norm_nonneg _) hC)

theorem exists_same_region_Q_first_xi_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ Cfirst : ℝ, 0 ≤ Cfirst ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p 2 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, i ≠ 1 → ∀ p ∈ S, |coordPartial 0 (heightQCoefficient g z i) p| ≤ Cfirst := by
  obtain ⟨C, hC, hQ⟩ := exists_local_fixedTime_Q_jet_bound G (max R Z) hG hd hc 2
  refine ⟨C * max 1 Z, mul_nonneg hC (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden i hi p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hpoint : coordinatePoint (qSpatialProjection (qSolutionJet z p) 0) (p 1) = p := point_eta p
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have hbound := hQ g U hg hU (p 1) (qSpatialProjection (qSolutionJet z p))
    (by simpa only [hpoint] using hSU hp)
    (by simpa only [hpoint] using hgB p hp)
    (by rw [he]; exact qSolutionJet_norm_bound_of_coordinateBound hR hz2 hcoords hp)
    (by simpa only [hpoint] using hdet p hp)
    (by rw [he, stateQDenominator_qSolutionJet]; exact hden p hp) 2 le_rfl
  exact heightQCoefficient_xi_bound_of_fixedTime_second hg hU hz hSU hzB hC hp hxx hbound i hi

end SmoothLocal.HighEquation

end

end OAI
