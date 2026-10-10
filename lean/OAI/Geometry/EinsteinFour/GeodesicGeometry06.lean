import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry05

namespace OAI


section

/-! Canceling the radial cubic measure against the actual exponential
Jacobian leaves the determinant of the normal Jacobi tensor itself. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

private theorem radial_cubic_cancel (a r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (r ^ 3) * ENNReal.ofReal |a / r ^ 3| = ENNReal.ofReal |a| := by
  rw [← ENNReal.ofReal_mul (pow_pos hr 3).le]
  congr 1
  rw [abs_div, abs_of_pos (pow_pos hr 3)]
  field_simp

theorem minimizing_exponential_integral_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    (∫⁻ v in actualMinimizingTangentDomain g o e,
      ENNReal.ofReal (frameExponentialJacobian g o e v)) =
    polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
        ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
        else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  classical
  let F : Directions × Ioi (0 : ℝ) → ℝ≥0∞ := fun p =>
    if p.2.val ≤ actualCutTime g
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1))) then
      ENNReal.ofReal |((actualJacobiSolution g hRic
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))).J p.2.val).det /
          p.2.val ^ 3| else 0
  have hF : Measurable F := by
    let S := actualMinimizingTangentDomain g o e
    let J := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)
    have hS : MeasurableSet S := (actualMinimizingTangentDomain_closed g o e).measurableSet
    have hJ : Measurable J := (ENNReal.continuous_ofReal.comp
      (frameExponentialJacobian_continuous g o e)).measurable
    have hf := (hJ.indicator hS).comp
      euclideanPolarReconstruction_measurePreserving.measurable
    convert hf using 1
    funext p
    have hiff := actualMinimizingTangentDomain_ray_iff g o e he p.1 p.2.val p.2.property.le
    by_cases hc : p.2.val ≤ actualCutTime g
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))
    · have hm : euclideanPolarReconstruction p ∈ S := hiff.mpr hc
      simp only [F, ite_eq_left hc, Function.comp_apply, Set.indicator_of_mem hm, J]
      exact (congrArg ENNReal.ofReal (frameExponentialJacobian_direction g o hRic e he
        p.1 p.2.val p.2.property)).symm
    · have hm : euclideanPolarReconstruction p ∉ S := fun hh => hc (hiff.mp hh)
      simp only [F, ite_eq_right hc, Function.comp_apply, Set.indicator_of_notMem hm]
  rw [minimizing_exponential_integral_polar g o hRic e he]
  change (∫⁻ p, F p ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3))) = _
  rw [lintegral_prod _ hF.aemeasurable, lintegral_smul_measure]
  congr 1
  apply lintegral_congr
  intro q
  have hrmeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val ^ 3)) := by
    fun_prop
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hrmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply lintegral_congr
  intro r
  dsimp [F]
  split_ifs with hc
  · exact radial_cubic_cancel _ r.val r.property
  · exact mul_zero _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact radial determinant integral over an exponential ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular MeasureTheory Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exponential_ball_integral_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) (R : ℝ) :
    (∫⁻ v in ball 0 R, ENNReal.ofReal (frameExponentialJacobian g o e v)) =
      polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
        (if r.val < R then ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
          else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  classical
  let J := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)
  let F : Directions × Ioi (0 : ℝ) → ℝ≥0∞ := fun p =>
    if p.2.val < R then ENNReal.ofReal |((actualJacobiSolution g hRic
      (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))).J p.2.val).det /
      p.2.val ^ 3| else 0
  have hJ : Measurable J := (ENNReal.continuous_ofReal.comp
    (frameExponentialJacobian_continuous g o e)).measurable
  have hid (p : Directions × Ioi (0 : ℝ)) :
      (ball 0 R).indicator J (euclideanPolarReconstruction p) = F p := by
    have hb : euclideanPolarReconstruction p ∈ ball (0 : FourSpace) R ↔ p.2.val < R := by
      rw [mem_ball, dist_zero_right, euclideanPolarReconstruction_norm]
    by_cases hp : p.2.val < R
    · rw [Set.indicator_of_mem (hb.mpr hp)]
      dsimp only [F,J]
      rw [ite_eq_left hp]
      exact congrArg ENNReal.ofReal (frameExponentialJacobian_direction g o hRic e he
        p.1 p.2.val p.2.property)
    · rw [Set.indicator_of_notMem (fun hh => hp (hb.mp hh))]
      exact (ite_eq_right hp).symm
  have hF : Measurable F := by
    have hh := (hJ.indicator (isOpen_ball.measurableSet : MeasurableSet (ball (0 : FourSpace) R))).comp
      euclideanPolarReconstruction_measurePreserving.measurable
    convert hh using 1
    funext p
    exact (hid p).symm
  calc
    _ = ∫⁻ v, (ball 0 R).indicator J v := (lintegral_indicator isOpen_ball.measurableSet J).symm
    _ = ∫⁻ p, (ball 0 R).indicator J (euclideanPolarReconstruction p)
        ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) :=
      (euclideanPolarReconstruction_measurePreserving.lintegral_comp
        (hJ.indicator isOpen_ball.measurableSet)).symm
    _ = ∫⁻ p, F p ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) :=
      lintegral_congr hid
    _ = _ := by
      rw [lintegral_prod _ hF.aemeasurable, lintegral_smul_measure]
      congr 1
      apply lintegral_congr
      intro q
      have hrmeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val ^ 3)) := by fun_prop
      rw [Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul_non_measurable _ hrmeas
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply lintegral_congr
      intro r
      dsimp [F]
      split_ifs with hc
      · have hr3 : 0 < r.val ^ 3 := pow_pos r.property 3
        rw [← ENNReal.ofReal_mul hr3.le]
        congr 1
        rw [abs_div, abs_of_pos hr3]
        field_simp [ne_of_gt (show 0 < r.val from r.property)]
      · exact mul_zero _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual polar volume bound at a fixed positive orthonormal frame.
The minimizing radial cutoff is bounded by the first conjugate time, and
the metric volume normalization is bounded by its sharp Euclidean value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem volumeMeasure_le_sphericalJacobi_lintegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ ENNReal.ofReal (2 * Real.pi ^ 2) *
      ∫⁻ q : Directions, ∫⁻ r in Icc (0 : ℝ) Real.pi,
        ENNReal.ofReal (actualRegularJacobi g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) r).truncatedDensity
        ∂volume ∂sphereMeasure := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he] at h
  calc
    volumeMeasure g univ ≤ riemannianChartFactor *
        (polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
          (if r.val ≤ actualCutTime g
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
            ENNReal.ofReal |((actualJacobiSolution g hRic
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
            else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure) := h
    _ ≤ 1 * (polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
          (if r.val ≤ actualCutTime g
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
            ENNReal.ofReal |((actualJacobiSolution g hRic
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
            else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure) := by
      gcongr
      exact riemannianChartFactor_le_one
    _ ≤ ENNReal.ofReal (2 * Real.pi ^ 2) *
        ∫⁻ q : Directions, ∫⁻ r in Icc (0 : ℝ) Real.pi,
          ENNReal.ofReal (actualRegularJacobi g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) r).truncatedDensity
          ∂volume ∂sphereMeasure := by
      rw [one_mul, polarAngularMass_eq]
      gcongr
      exact actualJacobi_cutoff_lintegral_le g hRic _ _
        (actualCutTime_le_firstConjugateTime g hRic _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weighted exponential-area domination.  The weight is retained through
actual polar coordinates, for use with scalar oscillations and energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

theorem euclidean_lintegral_polar (F : FourSpace → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v) = polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
      ENNReal.ofReal (r.val ^ 3) * F (r.val • q.val)
        ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  have hp := euclideanPolarReconstruction_measurePreserving.lintegral_comp hF
  have hm : Measurable (fun p : Directions × Ioi (0 : ℝ) =>
      F (euclideanPolarReconstruction p)) := by
    simpa only [Function.comp_apply] using!
      hF.comp euclideanPolarReconstruction_measurePreserving.measurable
  rw [← hp, lintegral_prod _ hm.aemeasurable, lintegral_smul_measure]
  congr 1
  apply lintegral_congr
  intro q
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (by fun_prop : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val ^ 3)))
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

private theorem radial_weight_cancel (a r : ℝ) (hr : 0 < r) (w : ℝ≥0∞) :
    ENNReal.ofReal (r ^ 3) * (ENNReal.ofReal |a / r ^ 3| * w) =
      ENNReal.ofReal |a| * w := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hr 3).le]
  congr 1
  rw [abs_div, abs_of_pos (pow_pos hr 3)]
  field_simp

theorem minimizing_exponential_weighted_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ v in actualMinimizingTangentDomain g o e,
      ENNReal.ofReal (frameExponentialJacobian g o e v) * W (frameExponential g o e v)) =
    polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
        ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| *
            W (frameExponential g o e (r.val • q.val))
        else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  classical
  let S := actualMinimizingTangentDomain g o e
  let F := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v) *
    W (frameExponential g o e v)
  have hS : MeasurableSet S := (actualMinimizingTangentDomain_closed g o e).measurableSet
  have hF : Measurable F :=
    ((ENNReal.continuous_ofReal.comp (frameExponentialJacobian_continuous g o e)).measurable).mul
      (hW.comp (frameExponential_continuous g o e).measurable)
  rw [← lintegral_indicator hS F, euclidean_lintegral_polar _ (hF.indicator hS)]
  congr 1
  apply lintegral_congr
  intro q
  apply lintegral_congr
  intro r
  have hiff := actualMinimizingTangentDomain_ray_iff g o e he q r.val r.property.le
  by_cases hc : r.val ≤ actualCutTime g
      (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
  · have hm : r.val • q.val ∈ S := hiff.mpr hc
    rw [ite_eq_left hc, Set.indicator_of_mem hm]
    dsimp only [F]
    rw [frameExponentialJacobian_direction g o hRic e he q r.val r.property]
    exact radial_weight_cancel _ _ r.property _
  · have hm : r.val • q.val ∉ S := fun h => hc (hiff.mp h)
    rw [ite_eq_right hc, Set.indicator_of_notMem hm, mul_zero]

variable [SecondCountableTopology M]

theorem volume_lintegral_le_weighted_exponential (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ y, W y ∂volumeMeasure g) ≤ riemannianChartFactor *
      ∫⁻ v in actualMinimizingTangentDomain g o e,
        ENNReal.ofReal (frameExponentialJacobian g o e v) * W (frameExponential g o e v) := by
  have h := lintegral_mono' (volumeMeasure_le_exponentialAreaMeasure g o hRic e he)
    (le_rfl : W ≤ W)
  rw [exponentialAreaMeasure, lintegral_smul_measure,
    lintegral_map hW (frameExponential_continuous g o e).measurable] at h
  have hj : Measurable (fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)) :=
    ENNReal.measurable_ofReal.comp (frameExponentialJacobian_continuous g o e).measurable
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hj
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [smul_eq_mul] using! h

theorem volume_lintegral_le_weighted_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ y, W y ∂volumeMeasure g) ≤ riemannianChartFactor * polarAngularMass *
      ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
        (if r.val ≤ actualCutTime g
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
          ENNReal.ofReal |((actualJacobiSolution g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| *
              W (frameExponential g o e (r.val • q.val))
          else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  have h := volume_lintegral_le_weighted_exponential g o hRic e he W hW
  rw [minimizing_exponential_weighted_radial g o hRic e he W hW, ← mul_assoc] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end

end OAI
