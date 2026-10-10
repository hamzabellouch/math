import Mathlib
import OAI.Geometry.IntegralFillings.Optimality.BallCoarea

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open BorelCoefficients BorelRestriction MassMeasure CurrentOperations

noncomputable def ambientCoord {d : ℕ} (i : Fin d) : Euc d → ℝ := EuclideanSpace.proj i
noncomputable def unitCoord {d : ℕ} (i : Fin d) (x : UnitBall d) : ℝ := ambientCoord i x.val

lemma ambientCoord_lipschitz {d : ℕ} (i : Fin d) : LipschitzWith 1 (ambientCoord i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [dist_eq_norm]
  change ‖(x-y) i‖ ≤ ‖x-y‖
  exact PiLp.norm_apply_le (x-y) i

lemma unitCoord_lipschitz {d : ℕ} (i : Fin d) : LipschitzWith 1 (unitCoord i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (ambientCoord_lipschitz i).dist_le_mul x.val y.val

lemma unitCoord_bound {d : ℕ} (i : Fin d) (x : UnitBall d) : |unitCoord i x| ≤ 1 := by
  have hx : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  exact (PiLp.norm_apply_le x.val i).trans hx

lemma unitCoord_boundedLip {d : ℕ} (i : Fin d) : BoundedLip (unitCoord i) :=
  ⟨⟨1,unitCoord_lipschitz i⟩,1,unitCoord_bound i⟩

lemma ballChart_jacobian_coords (d : ℕ) :
    (ballChart d).jacobian (fun i => unitCoord i) =ᵐ[volume.restrict (ballChart d).domain]
      fun _ => 1 := by
  have he (i : Fin d) : EqOn ((ballChart d).scalar (unitCoord i)) (ambientCoord i)
      (ballChart d).domain := by
    intro z hz
    rw [(ballChart d).scalar_eq hz]
    rfl
  filter_upwards [(ballChart d).ae_jacobian_eq_extensions ambientCoord_lipschitz he] with z hz
  rw [hz]
  have hM : (Matrix.of fun (i j : Fin d) =>
      fderiv ℝ (ambientCoord i) z (EuclideanSpace.single j 1)) = 1 := by
    ext i j
    change (fderiv ℝ (EuclideanSpace.proj i) z) (EuclideanSpace.single j 1) = _
    rw [ContinuousLinearMap.fderiv]
    simp [Matrix.one_apply]
  rw [hM,Matrix.det_one]

lemma innerBallCurrent_coords (d : ℕ) {t : ℝ} (ht : -1 < t) :
    innerBallCurrent d t (fun _ => 1) (fun i => unitCoord i) =
      (volume (Metric.ball (0 : Euc d) (-t))).toReal := by
  let C := ballChart d
  let E := {x : UnitBall d | t < radiusFunction d x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (radiusFunction_lipschitz d).continuous.measurable
  have had : Admissible (fun _ : UnitBall d => (1:ℝ)) (fun i => unitCoord i) :=
    ⟨BoundedLip.const 1,fun i => ⟨1,unitCoord_lipschitz i⟩⟩
  rw [innerBallCurrent, restrictCurrent_apply C.action_isMetricCurrent E had]
  rw [C.borelAction_eq_integral C.action_isMetricCurrent
    (currentMassMeasure_controls C.action_isMetricCurrent)
    (measurable_const.indicator hE) (show ∃ M : ℝ, ∀ x, |E.indicator (fun _ => (1:ℝ)) x| ≤ M from
      ⟨1,fun x => by by_cases hx : x ∈ E <;> simp [hx]⟩)
    (fun i => unitCoord i) had.2]
  calc (∫ z in C.domain, (C.multiplicity z : ℝ) * C.jacobian (fun i => unitCoord i) z *
      E.indicator (fun _ => (1:ℝ)) (C.paramExtended z)) =
      ∫ z in Metric.ball (0 : Euc d) 1,
        (Metric.ball (0 : Euc d) (-t)).indicator (fun _ => (1:ℝ)) z := by
        apply integral_congr_ae
        filter_upwards [ballChart_jacobian_coords d, ae_restrict_mem C.borel] with z hj hz
        have hp : radiusFunction d (C.paramExtended z) = -‖z‖ := by
          have hz' : z ∈ Metric.ball (0 : Euc d) 1 := hz
          simp [IntegerChart.paramExtended, hz', C, ballChart, radiusFunction]
        have he : C.paramExtended z ∈ E ↔ z ∈ Metric.ball (0 : Euc d) (-t) := by
          change t < radiusFunction d (C.paramExtended z) ↔ dist z 0 < -t
          rw [hp,dist_zero_right]
          constructor <;> intro h <;> linarith
        change (1:ℤ) * C.jacobian (fun i => unitCoord i) z * _ = _
        rw [Int.cast_one, hj, one_mul, one_mul]
        by_cases hh : z ∈ Metric.ball (0 : Euc d) (-t)
        · simp [hh,he.mpr hh]
        · simp [hh,not_congr he |>.mpr hh]
    _ = (volume (Metric.ball (0 : Euc d) (-t))).toReal := by
      rw [integral_indicator measurableSet_ball]
      simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
        Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_ball]
      rw [inter_eq_left.mpr (Metric.ball_subset_ball (show -t ≤ 1 by linarith))]

lemma omega_pos (d : ℕ) : 0 < omega d := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Euc d) (by norm_num)).ne'
    Metric.isBounded_ball.measure_lt_top.ne

lemma ball_volume_scaling (d : ℕ) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball (0 : Euc d) r)).toReal = omega d * r^d := by
  rw [Measure.addHaar_ball_of_pos volume 0 hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, omega]
  ring

lemma abs_apply_le_mass {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) {b : X → ℝ}
    {π : Fin k → X → ℝ} (hb : BoundedLip b) (hb1 : ∀ x, |b x| ≤ 1)
    (hπ : ∀ i, LipschitzWith 1 (π i)) : |T b π| ≤ mass T := by
  apply le_csInf
  · obtain ⟨μ,hμ,hctrl⟩ := hT.finiteMass
    exact ⟨μ.real univ, μ,hμ,hctrl,rfl⟩
  · rintro r ⟨μ,hμ,hctrl,rfl⟩
    let := hμ
    apply (hctrl b π hb hπ).trans
    calc (∫ x, |b x| ∂μ) ≤ ∫ _ : X, (1:ℝ) ∂μ :=
          integral_mono ((integrable_const (1:ℝ)).mono' hb.continuous.aestronglyMeasurable
            (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb1 x)).abs
            (integrable_const 1) hb1
      _ = μ.real univ := by simp

end SharpIntegralFillings.Optimality

end

end OAI
