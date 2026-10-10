import OAI.Geometry.IsometricImmersion.Estimates.UniversalQRaw
import OAI.Geometry.IsometricImmersion.Metrics.LocalMetricPCoefficients
import OAI.Geometry.IsometricImmersion.Darboux.QSegmentDomain
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem metricPBundle_sub_norm_bound {g g0 : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    {w w0 : DarbouxState} (hp : statePoint w = statePoint w0)
    (hw : statePoint w ∈ U) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hmetric : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g0 p i j - g p i j) (statePoint w)‖ ≤ epsilon)
    (hstate : ‖w0 - w‖ ≤ epsilon) :
    ‖metricPBundle g0 w0 - metricPBundle g w‖ ≤ epsilon := by
  have hwords (i j : Fin 2) (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
      |iteratedCoordPartial ds (fun p => g0 p i j) (statePoint w) -
        iteratedCoordPartial ds (fun p => g p i j) (statePoint w)| ≤ epsilon := by
    rw [← CoordinateBound.iterated_sub (hg0.1 i j) (hg.1 i j) hU ds hw]
    exact (norm_iteratedCoordPartial_le_jet ((hg0.1 i j).sub (hg.1 i j)) hU ds hw).trans
      (hmetric i j ds.length hds)
  have h0 : ‖g0 (statePoint w) - g (statePoint w)‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [] (by norm_num)
  have h1 : ‖(fun d i j => coordPartial d (fun p => g0 p i j) (statePoint w)) -
      (fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [d] (by norm_num)
  have h2 : ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g0 p i j)) (statePoint w)) -
      (fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro e
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [d, e] (by norm_num)
  change max ‖g0 (statePoint w0) - g (statePoint w)‖
    (max ‖(fun d i j => coordPartial d (fun p => g0 p i j) (statePoint w0)) -
      (fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖
      (max ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g0 p i j)) (statePoint w0)) -
        (fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖
        ‖w0 - w‖)) ≤ epsilon
  rw [← hp]
  exact max_le h0 (max_le h1 (max_le h2 hstate))

theorem metricPBundle_mem_baseTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|) :
    metricPBundle g w ∈ universalMetricBaseTube (max G W) d := by
  refine ⟨?_, hdet⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    metricPBundle_norm_bound hg hU hw hG hgB hwB

theorem qFirstCoefficient_five_eq_numerator {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qFirstCoefficient g 5 w = -stateNumerator g w / (stateQDenominator g w)^2 := by
  unfold qFirstCoefficient
  rw [sixVariableQ_xx_axis hg hU hw]
  simp only [stateNumerator, jetNumerator, stateMixed, stateEnergy, div_pow]
  ring

theorem exists_uniform_Q_metric_state_margins (G W : ℝ)
    {d nu eta beta kappa : ℝ} (hG : 0 ≤ G) (hd : 0 < d)
    (hnu : 0 < nu) (heta : 0 < eta) (hbeta : 0 < beta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ∀ w w0 : DarbouxState, statePoint w = statePoint w0 → statePoint w ∈ U →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g0 p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → ‖w0‖ ≤ W → d ≤ |(g (statePoint w)).det| → d ≤ |(g0 (statePoint w)).det| →
      (∀ i j k, k ≤ 2 →
        ‖iteratedFDeriv ℝ k (fun p => g0 p i j - g p i j) (statePoint w)‖ ≤ epsilon) →
      ‖w0 - w‖ ≤ epsilon → nu ≤ |stateQDenominator g w| → eta ≤ stateEnergy g w →
      stateNumerator g w ≤ -beta → gaussianCurvature g (statePoint w) ≤ -kappa →
      nu / 2 ≤ |stateQDenominator g0 w0| ∧ |stateQDenominator g0 w0| ≤ A ∧
      eta / 2 ≤ stateEnergy g0 w0 ∧
      (beta / 2) / A^2 ≤ qFirstCoefficient g0 5 w0 ∧
      ((kappa / 2) * (eta / 2)) / A^2 ≤
        (qFirstCoefficient g0 4 w0 / 2)^2 + qFirstCoefficient g0 5 w0 := by
  obtain ⟨epsilon, hepsilon, htransfer⟩ := universalQRaw_uniform_margins (max G W)
    hd hnu heta hbeta hkappa
  obtain ⟨A, hA, hAbound⟩ := universalQDenominator_uniform_bound (max G W) hd
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 U hg hg0 hU w w0 hp hw hgB hg0B hwB hw0B hdet hdet0 hmetric hstate
    hden henergy hnum hK
  have hw0 : statePoint w0 ∈ U := by rw [← hp]; exact hw
  have ha := metricPBundle_mem_baseTube hg hU hw hG hgB hwB hdet
  have hb := metricPBundle_mem_baseTube hg0 hU hw0 hG
    (by simpa only [← hp] using hg0B) hw0B (by simpa only [← hp] using hdet0)
  have hab := metricPBundle_sub_norm_bound hg hg0 hU hp hw hepsilon.le hmetric hstate
  have hmargin := htransfer _ ha _ hb hab
    (by simpa only [universalQDenominator_metricPBundle] using hden)
    (by simpa only [universalEnergy_metricPBundle] using henergy)
    (by simpa only [universalQNumerator_metricPBundle hg hU hw] using hnum)
    (by simpa only [universalQCurvature_metricPBundle hg hU hw] using hK)
  have hd0 : nu / 2 ≤ |stateQDenominator g0 w0| := by
    simpa only [universalQDenominator_metricPBundle] using hmargin.1
  have hE0 : eta / 2 ≤ stateEnergy g0 w0 := by
    simpa only [universalEnergy_metricPBundle] using hmargin.2.1
  have hN0 : stateNumerator g0 w0 ≤ -(beta / 2) := by
    simpa only [universalQNumerator_metricPBundle hg0 hU hw0] using hmargin.2.2.1
  have hK0 : gaussianCurvature g0 (statePoint w0) ≤ -(kappa / 2) := by
    simpa only [universalQCurvature_metricPBundle hg0 hU hw0] using hmargin.2.2.2
  have hupper : |stateQDenominator g0 w0| ≤ A := by
    simpa only [universalQDenominator_metricPBundle] using hAbound _ hb
  have hne : stateQDenominator g0 w0 ≠ 0 :=
    abs_pos.mp ((half_pos hnu).trans_le hd0)
  have hdomain : w0 ∈ darbouxQStateDomain g0 U := ⟨hw0, hne⟩
  have hsq : (stateQDenominator g0 w0)^2 ≤ A^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1).trans hA)).mpr hupper
  refine ⟨hd0, hupper, hE0, ?_, ?_⟩
  · rw [qFirstCoefficient_five_eq_numerator hg0 hU hdomain]
    have hnumle : beta / 2 ≤ -stateNumerator g0 w0 := by
      simpa only [neg_neg] using neg_le_neg hN0
    exact div_le_div₀ ((half_pos hbeta).le.trans hnumle) hnumle (sq_pos_of_ne_zero hne) hsq
  · rw [q_principal_discriminant hg0 hU hdomain]
    have hk : kappa / 2 ≤ -gaussianCurvature g0 (statePoint w0) := by
      simpa only [neg_neg] using neg_le_neg hK0
    have hprod : (kappa / 2) * (eta / 2) ≤
        -(gaussianCurvature g0 (statePoint w0) * stateEnergy g0 w0) := by
      simpa only [neg_mul] using
        mul_le_mul hk hE0 (half_pos heta).le ((half_pos hkappa).le.trans hk)
    exact div_le_div₀
      ((mul_nonneg (half_pos hkappa).le (half_pos heta).le).trans hprod)
      hprod (sq_pos_of_ne_zero hne) hsq

end SmoothLocal.HighEquation

end

end OAI
