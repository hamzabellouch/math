import OAI.Geometry.EinsteinFour.GeodesicGeometry06
import OAI.Geometry.EinsteinFour.ScalarRegularity06

namespace OAI


section

/-! Averaging the lower polar integral over the actual frame probability. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def actualBallRadialMass (g : SmoothMetric M) (hRic : RicciThree g) (R : ℝ)
    (e : FrameBundle g) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det|

theorem measurable_actualBallRadialMass (g : SmoothMetric M) (hRic : RicciThree g) (R : ℝ) :
    Measurable (actualBallRadialMass g hRic R) := by
  have h := ENNReal.measurable_ofReal.comp
    (actualJacobiJ_joint_continuous g hRic).matrix_det.abs.measurable
  exact (h.comp measurable_swap).lintegral_prod_right'

theorem actualBallRadialMass_subtype (g : SmoothMetric M) (hRic : RicciThree g)
    (R : ℝ) (e : FrameBundle g) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val < R then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det| else 0)
      ∂((volume : Measure ℝ).comap Subtype.val)) = actualBallRadialMass g hRic R e := by
  let F : ℝ → ℝ≥0∞ := fun r =>
    if r < R then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  change (∫⁻ r : Ioi (0 : ℝ), F r.val ∂((volume : Measure ℝ).comap Subtype.val)) = _
  rw [lintegral_subtype_comap measurableSet_Ioi F, ← lintegral_indicator measurableSet_Ioi]
  rw [actualBallRadialMass, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases h0 : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from h0)]
    by_cases hR : r < R
    · rw [Set.indicator_of_mem (show r ∈ Ioo (0 : ℝ) R from ⟨h0,hR⟩)]
      exact ite_eq_left hR
    · rw [Set.indicator_of_notMem (fun h => hR h.2)]
      exact ite_eq_right hR
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from h0),
      Set.indicator_of_notMem (fun h => h0 h.1)]

theorem exponential_ball_integral_radial_mass (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (R : ℝ) :
    (∫⁻ v in ball 0 R, ENNReal.ofReal (frameExponentialJacobian g o e v)) =
      polarAngularMass * ∫⁻ q : Directions,
        actualBallRadialMass g hRic R
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure := by
  rw [exponential_ball_integral_radial g o hRic e he]
  simp_rw [actualBallRadialMass_subtype]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

theorem lower_canonical_radial_mass_le_volume (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (R : ℝ)
    (hinj : ∀ e ∈ o.positive, InjOn (frameExponential g o e) (ball 0 R)) :
    (riemannianChartFactor * polarAngularMass) *
      (∫⁻ e, actualBallRadialMass g hRic R e ∂canonicalFrameMeasure g o) ≤ volumeMeasure g univ := by
  have hc : riemannianChartFactor * polarAngularMass ≠ ⊤ := by
    apply ENNReal.mul_ne_top _ polarAngularMass_ne_top
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hs (e : FrameBundle g) (he : e ∈ o.positive) :
      (riemannianChartFactor * polarAngularMass) *
        (∫⁻ q : Directions, actualBallRadialMass g hRic R
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure) ≤
      volumeMeasure g univ := by
    have h := exponential_ball_integral_le_volume g o e R (hinj e he)
    rw [exponential_ball_integral_radial_mass g o hRic e he R, ← mul_assoc] at h
    exact h
  have h := lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono hs)
  rw [lintegral_const_mul' _ _ hc, canonicalFrame_lintegral_sphere_rotations g o _
    (measurable_actualBallRadialMass g hRic R), lintegral_const,
    show canonicalFrameMeasure g o univ = 1 from measure_univ, mul_one] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end

end OAI
