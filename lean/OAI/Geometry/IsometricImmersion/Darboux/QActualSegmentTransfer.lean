import OAI.Geometry.IsometricImmersion.Darboux.QMetricJetTransfer
import OAI.Geometry.IsometricImmersion.Darboux.QSegmentAveraging

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qSolutionJet_norm_bound {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    {R Z : ℝ} (hR : 0 ≤ R) (_hZ : 0 ≤ Z) (hpB : ‖p‖ ≤ R)
    (hzB : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hw (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
      |iteratedCoordPartial ds z p| ≤ Z :=
    (norm_iteratedCoordPartial_le_jet hz hU ds hp).trans (hzB ds.length hds)
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hw [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [0, 0] (by norm_num)).trans (le_max_right _ _)

theorem qSolutionJet_sub_norm_of_word_difference {z z0 : Coord → ℝ} {p : Coord}
    {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hjet : ∀ ds : List (Fin 2), ds.length ≤ 2 →
      |iteratedCoordPartial ds z0 p - iteratedCoordPartial ds z p| ≤ epsilon) :
    ‖qSolutionJet z0 p - qSolutionJet z p‖ ≤ epsilon :=
  state_distance_le_of_coordinate_error he
    (qSolutionJet_coordinate_error z z0 p he
      (fun i => hjet [i] (by norm_num)) (hjet [0, 1] (by norm_num))
      (hjet [0, 0] (by norm_num)))

theorem stateSegment_norm_le {w0 w1 : DarbouxState} {W sigma : ℝ}
    (h0 : ‖w0‖ ≤ W) (h1 : ‖w1‖ ≤ W) (hs : sigma ∈ Icc (0 : ℝ) 1) :
    ‖stateSegment w0 w1 sigma‖ ≤ W := by
  have hs0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hs.2
  calc
    _ ≤ ‖(1 - sigma) • w0‖ + ‖sigma • w1‖ := norm_add_le _ _
    _ = (1 - sigma) * ‖w0‖ + sigma * ‖w1‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs0, abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * W + sigma * W :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hs0) (mul_le_mul_of_nonneg_left h1 hs.1)
    _ = W := by ring

theorem stateSegment_sub_right_norm_le {w0 w1 : DarbouxState} {sigma : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) :
    ‖stateSegment w0 w1 sigma - w1‖ ≤ ‖w0 - w1‖ := by
  have he : stateSegment w0 w1 sigma - w1 = (1 - sigma) • (w0 - w1) := by
    ext i
    simp only [stateSegment, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hs.1])

theorem stateNumerator_qSolutionJet_eq_product {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    stateNumerator g (qSolutionJet z p) = covHessian g z p 0 0 * covHessian g z p 1 1 := by
  have hd : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1)^2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold stateNumerator jetNumerator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  change (jetMixed g p (coordPartial 0 (coordPartial 1 z) p)
    (fun i => coordPartial i z p))^2 +
      gaussianCurvature g p * jetEnergy g p (fun i => coordPartial i z p) = _
  rw [jetMixed_at_height, jetEnergy_at_height hg hp z]
  linarith

theorem stateNumerator_negative_of_solution_floors {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    {nu c : ℝ} (_hnu : 0 < nu) (hc : 0 < c)
    (hxx : nu ≤ |covHessian g z p 0 0|) (hyy : c ≤ |covHessian g z p 1 1|)
    (htime : (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0) :
    stateNumerator g (qSolutionJet z p) ≤ -(nu * c) := by
  have hyne : covHessian g z p 1 1 ≠ 0 := abs_pos.mp (hc.trans_le hyy)
  have hratio : covHessian g z p 0 0 / covHessian g z p 1 1 < 0 := by
    rw [← hessian_time_ratio hg hU hz hp hyne hD]
    exact htime
  have heq : covHessian g z p 0 0 * covHessian g z p 1 1 =
      (covHessian g z p 0 0 / covHessian g z p 1 1) * (covHessian g z p 1 1)^2 := by
    field_simp [hyne]
  have hneg : covHessian g z p 0 0 * covHessian g z p 1 1 < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos hratio (sq_pos_of_ne_zero hyne)
  have hprod := mul_le_mul hxx hyy hc.le (abs_nonneg _)
  rw [← abs_mul, abs_of_neg hneg] at hprod
  rw [stateNumerator_qSolutionJet_eq_product hg hU hz hp hD]
  linarith

theorem exists_uniform_actual_Q_segment_transfer (G R Z : ℝ)
    {d nu c eta kappa : ℝ} (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hd : 0 < d) (hnu : 0 < nu) (hc : 0 < c) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (z z0 : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ContDiffOn ℝ ∞ z U → ContDiffOn ℝ ∞ z0 U →
      ∀ p ∈ U, ‖p‖ ≤ R →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun x => g x i j) p‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun x => g0 x i j) p‖ ≤ G) →
      (∀ k ≤ 2, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ k ≤ 2, ‖iteratedFDeriv ℝ k z0 p‖ ≤ Z) →
      d ≤ |(g p).det| → d ≤ |(g0 p).det| →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun x => g0 x i j - g x i j) p‖ ≤ epsilon) →
      (∀ ds : List (Fin 2), ds.length ≤ 2 →
        |iteratedCoordPartial ds z0 p - iteratedCoordPartial ds z p| ≤ epsilon) →
      nu ≤ |covHessian g z p 0 0| → c ≤ |covHessian g z p 1 1| →
      eta ≤ heightEnergy g z p → gaussianCurvature g p ≤ -kappa →
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p →
      (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0 →
      ∀ sigma ∈ Icc (0 : ℝ) 1,
      nu / 2 ≤ |stateQDenominator g0 (qHeightJetSegment z0 z sigma p)| ∧
      |stateQDenominator g0 (qHeightJetSegment z0 z sigma p)| ≤ A ∧
      eta / 2 ≤ stateEnergy g0 (qHeightJetSegment z0 z sigma p) ∧
      ((nu * c) / 2) / A^2 ≤ qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma p) ∧
      ((kappa / 2) * (eta / 2)) / A^2 ≤
        (qFirstCoefficient g0 4 (qHeightJetSegment z0 z sigma p) / 2)^2 +
          qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma p) := by
  obtain ⟨epsilon, A, hepsilon, hA, htransfer⟩ :=
    exists_uniform_Q_metric_state_margins G (max R Z) hG hd hnu heta
      (mul_pos hnu hc) hkappa
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 z z0 U hg hg0 hU hz hz0 p hp hpB hgB hg0B hzB hz0B
    hdet hdet0 hmetric hjet hxx hyy henergy hK hD htime sigma hs
  have hwB := qSolutionJet_norm_bound hz hU hp hR hZ hpB hzB
  have hw0B := qSolutionJet_norm_bound hz0 hU hp hR hZ hpB hz0B
  have hsegmentB := stateSegment_norm_le hw0B hwB hs
  have hstate : ‖qHeightJetSegment z0 z sigma p - qSolutionJet z p‖ ≤ epsilon :=
    (stateSegment_sub_right_norm_le hs).trans
      (qSolutionJet_sub_norm_of_word_difference hepsilon.le hjet)
  have hbase : statePoint (qSolutionJet z p) = statePoint (qHeightJetSegment z0 z sigma p) := by
    rw [statePoint_qSolutionJet, statePoint_qHeightJetSegment]
  have hnum := stateNumerator_negative_of_solution_floors hg hU hz hp hD hnu hc hxx hyy htime
  apply htransfer g g0 U hg hg0 hU (qSolutionJet z p) (qHeightJetSegment z0 z sigma p)
    hbase (by simpa only [statePoint_qSolutionJet] using hp)
    (by simpa only [statePoint_qSolutionJet] using hgB)
    (by simpa only [statePoint_qSolutionJet] using hg0B) hwB hsegmentB
    (by simpa only [statePoint_qSolutionJet] using hdet)
    (by simpa only [statePoint_qSolutionJet] using hdet0)
    (by simpa only [statePoint_qSolutionJet] using hmetric) hstate
    (by simpa only [stateQDenominator_qSolutionJet] using hxx) ?_ hnum
    (by simpa only [statePoint_qSolutionJet] using hK)
  unfold stateEnergy
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet, jetEnergy_at_height hg hp z]
  exact henergy

end SmoothLocal.HighEquation

end

end OAI
