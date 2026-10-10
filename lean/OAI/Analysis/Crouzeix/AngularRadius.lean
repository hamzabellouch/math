import Mathlib
import OAI.Analysis.Crouzeix.CircleAnalytic

namespace OAI

/-! Angular Radius. -/

noncomputable section

open Set Filter Metric Topology Function Complex MeasureTheory

namespace CrouzeixHilbert.Boundary

lemma integral_scaled_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (R : ℝ) :
    (∫ t, f ((R : ℂ) * circleCoordinate t) ∂circleMeasure) = Real.circleAverage f 0 R := by
  rw [integral_circleCoordinate_eq_circleAverage (fun z => f ((R : ℂ) * z))]
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [circleMap, zero_add, ofReal_one, one_mul]

lemma integral_scaled_coordinate_cauchy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) {R : ℝ} (hR : 0 < R) :
    (∫ t, ((R : ℂ) * circleCoordinate t) • f ((R : ℂ) * circleCoordinate t)
        ∂circleMeasure) =
      (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(0, R), f z) := by
  rw [integral_scaled_circleCoordinate (fun z => z • f z) R,
    Real.circleAverage_eq_circleIntegral hR.ne']
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro z hz
  have hn : z ≠ 0 := norm_pos_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hz]; exact hR)
  simp only [sub_zero, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma integral_scaled_deform {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {f : ℂ → E}
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : DifferentiableOn ℂ f (ball 0 R \ closedBall 0 r)) :
    (∫ t, ((R : ℂ) * circleCoordinate t) • f ((R : ℂ) * circleCoordinate t)
      ∂circleMeasure) =
    ∫ t, ((r : ℂ) * circleCoordinate t) • f ((r : ℂ) * circleCoordinate t)
      ∂circleMeasure := by
  rw [integral_scaled_coordinate_cauchy f (hr.trans_le hrR),
    integral_scaled_coordinate_cauchy f hr]
  congr 1
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty hc
  intro z hz
  exact (hd z hz.1).differentiableAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz.1)

lemma integral_laurent_deform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {f : ℂ → E}
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : DifferentiableOn ℂ f (ball 0 R \ closedBall 0 r)) (j : ℤ) :
    (∫ t, (((R : ℂ) * circleCoordinate t)^j) • f ((R : ℂ) * circleCoordinate t)
      ∂circleMeasure) =
    ∫ t, (((r : ℂ) * circleCoordinate t)^j) • f ((r : ℂ) * circleCoordinate t)
      ∂circleMeasure := by
  have hn {z : ℂ} (hz : z ∈ closedBall 0 R \ ball 0 r) : z ≠ 0 := by
    have hle : r ≤ ‖z‖ := not_lt.mp (mt mem_ball_zero_iff.mpr hz.2)
    exact norm_pos_iff.mp (hr.trans_le hle)
  have hh := integral_scaled_deform hr hrR
    (f := fun z => z^(j-1) • f z)
    ((continuousOn_id.zpow₀ (j-1) (fun z hz => Or.inl (hn hz))).smul hc)
    ((((differentiableOn_id (𝕜 := ℂ)).zpow (Or.inl (fun z hz => hn ⟨ball_subset_closedBall hz.1,
      fun h => hz.2 (ball_subset_closedBall h)⟩)))).smul hd)
  have hs {z : ℂ} (hz : z ≠ 0) : z * z^(j-1) = z^j := by
    rw [← zpow_one_add₀ hz]
    congr 1
    omega
  have hRz (t : CircleSpace) : (R : ℂ) * circleCoordinate t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr (hr.trans_le hrR).ne') (circleCoordinate_ne_zero t)
  have hrz (t : CircleSpace) : (r : ℂ) * circleCoordinate t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (circleCoordinate_ne_zero t)
  simpa only [smul_smul, hs (hRz _), hs (hrz _)] using hh

end CrouzeixHilbert.Boundary

end

end OAI
