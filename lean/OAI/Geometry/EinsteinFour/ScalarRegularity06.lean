import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.GeodesicGeometry06
import OAI.Geometry.EinsteinFour.MetricInverseCalculus
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelBesselEstimate
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMeasure
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelUniqueness
import OAI.Geometry.EinsteinFour.ScalarSecondDerivativeMinimum
import OAI.Geometry.EinsteinFour.WeylEstimates03
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1

namespace OAI


section

/-! Averaging the actual polar bound over the canonical frame probability.
Right invariance under each oriented rotation removes the angular average;
Tonelli then puts the time and frame integrals in the manuscript's order. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability

theorem canonicalFrame_lintegral_sphere_rotations (g : SmoothMetric M)
    (o : FrameOrientation g) (F : FrameBundle g → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ e, ∫⁻ q : Directions,
      F (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
      ∂sphereMeasure ∂canonicalFrameMeasure g o) =
      ∫⁻ e, F e ∂canonicalFrameMeasure g o := by
  have hm : Measurable (fun p : FrameBundle g × Directions =>
      F (p.1.rotate (orientedToOrthogonal (directionOrientedMatrix p.2)))) :=
    hF.comp ((continuous_frameRotate g).comp
      (continuous_fst.prodMk (continuous_orientedToOrthogonal.comp
        (continuous_directionOrientedMatrix.comp continuous_snd)))).measurable
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hq (q : Directions) :
      (∫⁻ e, F (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
        ∂canonicalFrameMeasure g o) = ∫⁻ e, F e ∂canonicalFrameMeasure g o :=
    (canonicalFrameMeasure_rotate g o (directionOrientedMatrix q)).lintegral_comp hF
  simp_rw [hq]
  simp

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem measurable_actualJacobiDensity (g : SmoothMetric M) (hRic : RicciThree g) :
    Measurable (fun p : ℝ × FrameBundle g =>
      (actualRegularJacobi g hRic p.2 p.1).truncatedDensity) := by
  simpa only [actualRegularJacobi_truncatedDensity_eq] using
    measurable_truncatedJacobiDensity (actualJacobiMatrix g hRic)
      (actualJacobiJ_joint_continuous g hRic)

def actualRadialMass (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) Real.pi,
    ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem measurable_actualRadialMass (g : SmoothMetric M) (hRic : RicciThree g) :
    Measurable (actualRadialMass g hRic) := by
  have h := ENNReal.measurable_ofReal.comp (measurable_actualJacobiDensity g hRic)
  exact (h.comp measurable_swap).lintegral_prod_right'

theorem canonical_actualRadialMass_integral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    (∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o) =
      ∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
        ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity
        ∂canonicalFrameMeasure g o := by
  have h := ENNReal.measurable_ofReal.comp (measurable_actualJacobiDensity g hRic)
  exact lintegral_lintegral_swap (h.comp measurable_swap).aemeasurable

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem volumeMeasure_le_canonicalRadialMass (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    volumeMeasure g univ ≤ ENNReal.ofReal (2 * Real.pi ^ 2) *
      ∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o := by
  have h := lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono
    (fun e he => volumeMeasure_le_sphericalJacobi_lintegral g o hRic e he))
  change (∫⁻ _e, volumeMeasure g univ ∂canonicalFrameMeasure g o) ≤
    ∫⁻ e, ENNReal.ofReal (2 * Real.pi ^ 2) *
      (∫⁻ q : Directions,
        actualRadialMass g hRic (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
        ∂sphereMeasure) ∂canonicalFrameMeasure g o at h
  simpa only [lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    canonicalFrame_lintegral_sphere_rotations g o _ (measurable_actualRadialMass g hRic)] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform finite radial domination constant, obtained from compactness of
the actual Jacobi family.  No curvature comparison estimate is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_uniform_actualJacobi_det_bound (g : SmoothMetric M) (hRic : RicciThree g) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let F : C(Icc (0 : ℝ) Real.pi × FrameBundle g, ℝ) :=
    ⟨fun p => ((actualJacobiSolution g hRic p.2).J p.1.val).det,
      ((actualJacobiJ_joint_continuous g hRic).comp
        (continuous_subtype_val.prodMap continuous_id)).matrix_det⟩
  refine ⟨‖F‖ + 1, by positivity, ?_⟩
  intro e r hr
  exact (F.norm_coe_le_norm (⟨r, hr⟩, e)).trans (by linarith)

variable [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [SecondCountableTopology M]

theorem volume_lintegral_le_bounded_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ y, W y ∂volumeMeasure g) ≤
      riemannianChartFactor * polarAngularMass * ENNReal.ofReal C *
        ∫⁻ q : Directions, ∫⁻ r in Icc (0 : ℝ) Real.pi,
          W (frameExponential g o e (r • q.val)) ∂volume ∂sphereMeasure := by
  have h := volume_lintegral_le_weighted_radial g o hRic e he W hW
  let F : Directions → ℝ → ℝ≥0∞ := fun q r => W (frameExponential g o e (r • q.val))
  have hstep (q : Directions) :
      (∫⁻ r : Ioi (0 : ℝ),
        (if r.val ≤ actualCutTime g
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
          ENNReal.ofReal |((actualJacobiSolution g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| * F q r.val
          else 0) ∂((volume : Measure ℝ).comap Subtype.val)) ≤
      ENNReal.ofReal C * ∫⁻ r in Icc (0 : ℝ) Real.pi, F q r := by
    have hpoint (r : Ioi (0 : ℝ)) :
        (if r.val ≤ actualCutTime g
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
          ENNReal.ofReal |((actualJacobiSolution g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| * F q r.val
          else 0) ≤ ENNReal.ofReal C * (Icc (0 : ℝ) Real.pi).indicator (F q) r.val := by
      split_ifs with hr
      · have hri : r.val ∈ Icc (0 : ℝ) Real.pi := ⟨r.property.le,
          hr.trans (actualCutTime_le_pi g hRic _)⟩
        rw [Set.indicator_of_mem hri]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hbound _ _ hri)) _
      · exact zero_le
    calc
      _ ≤ ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal C *
          (Icc (0 : ℝ) Real.pi).indicator (F q) r.val
            ∂((volume : Measure ℝ).comap Subtype.val) := lintegral_mono hpoint
      _ = ENNReal.ofReal C * ∫⁻ r in Ioi (0 : ℝ),
          (Icc (0 : ℝ) Real.pi).indicator (F q) r := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_subtype_comap measurableSet_Ioi]
      _ ≤ ENNReal.ofReal C * ∫⁻ r, (Icc (0 : ℝ) Real.pi).indicator (F q) r := by
        exact mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _
      _ = _ := by rw [lintegral_indicator measurableSet_Icc]
  calc
    _ ≤ riemannianChartFactor * polarAngularMass *
        ∫⁻ q : Directions, ENNReal.ofReal C *
          (∫⁻ r in Icc (0 : ℝ) Real.pi, F q r) ∂sphereMeasure :=
      h.trans (mul_le_mul_right (lintegral_mono hstep) _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Discharge of the published polar-volume input for the actual metric,
actual Jacobi solution and canonical frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actualJacobi_average_integrableOn (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a b : ℝ) :
    IntegrableOn (fun r => ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
      ∂canonicalFrameMeasure g o) (Icc a b) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have h := (integrable_truncatedJacobiDensity_product (canonicalFrameMeasure g o)
    (actualJacobiMatrix g hRic) (actualJacobiJ_joint_continuous g hRic) a b).integral_prod_left
  simpa only [actualRegularJacobi_truncatedDensity_eq] using! h

theorem actualJacobi_average_nonneg (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
      ∂canonicalFrameMeasure g o := by
  apply integral_nonneg
  intro e
  exact (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr

theorem canonical_actualRadialMass_eq (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    (∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o) =
      ENNReal.ofReal (∫ r in Icc (0 : ℝ) Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o) := by
  rw [canonical_actualRadialMass_integral]
  have hn : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) Real.pi),
      0 ≤ ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
        ∂canonicalFrameMeasure g o := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  rw [ofReal_integral_eq_lintegral_ofReal
    (actualJacobi_average_integrableOn g o hRic 0 Real.pi) hn]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  symm
  exact ofReal_integral_eq_lintegral_ofReal (actualJacobiDensity_integrable g o hRic r)
    (Filter.Eventually.of_forall fun e =>
      (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr.1)

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem totalVolume_le_actualJacobiIntegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    totalVolume g ≤ (2 * Real.pi ^ 2) *
      ∫ r in (0 : ℝ)..Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o := by
  have h := volumeMeasure_le_canonicalRadialMass g o hRic
  rw [canonical_actualRadialMass_eq, ← ENNReal.ofReal_mul (by positivity)] at h
  have hn : 0 ≤ (2 * Real.pi ^ 2) *
      ∫ r in Icc (0 : ℝ) Real.pi, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  have hreal := ENNReal.toReal_le_of_le_ofReal hn h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    at hreal
  exact hreal

theorem actualJacobiPolarInput_proved (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) : ActualJacobiPolarInput g o hRic := by
  let F : ℝ → ℝ := fun r => ∫ e,
    (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o
  have hvolume : totalVolume g ≤ (2 * Real.pi ^ 2) * ∫ r in (0 : ℝ)..Real.pi, F r :=
    totalVolume_le_actualJacobiIntegral g o hRic
  have hscale : (∫ r in (0 : ℝ)..Real.pi, F r) =
      Real.pi * ∫ u in (0 : ℝ)..1, F (Real.pi * u) := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) F Real.pi
    simpa only [smul_eq_mul, mul_zero, mul_one] using h.symm
  rw [hscale] at hvolume
  have hsplit : (∫ u in (0 : ℝ)..1, F (Real.pi * u)) =
      (∫ u in (0 : ℝ)..(5 / 8), F (Real.pi * u)) +
        ∫ u in (5 / 8 : ℝ)..1, F (Real.pi * u) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (actualJacobiDensity_intervalIntegrable g o hRic 0 (5 / 8) (by norm_num))
      (actualJacobiDensity_intervalIntegrable g o hRic (5 / 8) 1 (by norm_num))
  rw [hsplit] at hvolume
  change totalVolume g / (8 * Real.pi ^ 2 / 3) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < 8 * Real.pi ^ 2 / 3)).mpr
  convert hvolume using 1
  dsimp only [F]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L² translation bound as a scalar oscillation integral, averaged over
the actual spherical directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff BigOperators ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem smoothScalar_flow_oscillation_bound (d : ParallelMetricData g μ)
    (i : Fin 4) (hzero : ∀ e, (d.flow i).map 0 e = e)
    (a : SmoothScalar (M := M)) (t : ℝ) :
    (∫⁻ e, ENNReal.ofReal ((a.val ((d.flow i).map t e).base - a.val e.base) ^ 2) ∂μ) ≤
      ENNReal.ofReal (t ^ 2 * ‖smoothScalarGradientL2 d i a‖ ^ 2) := by
  let F := scalarTranslatedField d i t (smoothScalarValue g a) - smoothScalarValue g a
  have hi : Integrable (fun e => F e ^ 2) μ :=
    (F.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫⁻ e, ENNReal.ofReal (F e ^ 2) ∂μ) =
      ENNReal.ofReal (‖ContinuousMap.toLp 2 μ ℝ F‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun e => sq_nonneg (F e)))]
    congr 1
    rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards [] with e
    simp only [conj_trivial, pow_two]
  change (∫⁻ e, ENNReal.ofReal (F e ^ 2) ∂μ) ≤ _
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have h := smoothScalar_flow_translation_bound d i hzero a t
  have hF : ContinuousMap.toLp 2 μ ℝ F =
      scalarFlowTranslation d i t (smoothScalarValueL2 g μ a) - smoothScalarValueL2 g μ a := by
    dsimp only [F]
    rw [map_sub, ← scalarFlowTranslation_toLp]
    rfl
  rw [hF]
  calc
    _ ≤ (|t| * ‖smoothScalarGradientL2 d i a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mpr h
    _ = _ := by rw [mul_pow, sq_abs]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarOscillation_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def scalarGeodesicOscillation (g : SmoothMetric M) (a : SmoothScalar (M := M))
    (t : ℝ) (e : FrameBundle g) : ℝ≥0∞ :=
  ENNReal.ofReal ((a.val (parallelFrameFlowMap g 0 t e).base - a.val e.base) ^ 2)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarGeodesicOscillation_joint_continuous (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) :
    Continuous (fun p : ℝ × FrameBundle g => scalarGeodesicOscillation g a p.1 p.2) :=
  ENNReal.continuous_ofReal.comp
    ((((a.property.continuous.comp (continuous_frameBase g)).comp
      (parallelFrameFlowMap_continuous g 0)).sub
        ((a.property.continuous.comp (continuous_frameBase g)).comp continuous_snd)).pow 2)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarGeodesicOscillation_measurable (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) (t : ℝ) : Measurable (scalarGeodesicOscillation g a t) := by
  apply Continuous.measurable
  exact ENNReal.continuous_ofReal.comp
    ((((a.property.continuous.comp (continuous_frameBase g)).comp
      (parallelFrameFlowMap_continuous_slice g 0 t)).sub
        (a.property.continuous.comp (continuous_frameBase g))).pow 2)

theorem scalarGeodesicOscillation_sphere_average (g : SmoothMetric M)
    (o : FrameOrientation g) (a : SmoothScalar (M := M)) (t : ℝ) :
    (∫⁻ e, ∫⁻ q : Directions,
      ENNReal.ofReal ((a.val (frameExponential g o e (t • q.val)) - a.val e.base) ^ 2)
        ∂sphereMeasure ∂canonicalFrameMeasure g o) =
      ∫⁻ e, scalarGeodesicOscillation g a t e ∂canonicalFrameMeasure g o := by
  have h := canonicalFrame_lintegral_sphere_rotations g o
    (scalarGeodesicOscillation g a t) (scalarGeodesicOscillation_measurable g a t)
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [canonicalFrameMeasure_supported g o] with e he
  apply lintegral_congr
  intro q
  rw [frameExponential_direction_ray g o e he q t]
  rfl

theorem scalarGeodesicOscillation_integral_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) (t : ℝ) :
    (∫⁻ e, scalarGeodesicOscillation g a t e ∂canonicalFrameMeasure g o) ≤
      ENNReal.ofReal (t ^ 2 *
        ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hz : ∀ e, ((canonicalParallelMetricData g o hRic).flow 0).map 0 e = e :=
    fun e => actualParallelMetricData_zero g (canonicalFrameMeasure g o)
      (parallelFrameFlowMap_measurePreserving g o) hRic 0 e
  simpa only [scalarGeodesicOscillation] using!
    smoothScalar_flow_oscillation_bound (canonicalParallelMetricData g o hRic) 0 hz a t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global scalar pair oscillations are bounded by radial flow oscillations.
The measure comparison and all curves here are those of the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def scalarRadialOscillation (g : SmoothMetric M) (a : SmoothScalar (M := M))
    (e : FrameBundle g) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) Real.pi, scalarGeodesicOscillation g a r e

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarRadialOscillation_measurable (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) : Measurable (scalarRadialOscillation g a) :=
  ((scalarGeodesicOscillation_joint_continuous g a).measurable.comp
    measurable_swap).lintegral_prod_right'

theorem scalarRadialOscillation_integral (g : SmoothMetric M)
    (o : FrameOrientation g) (a : SmoothScalar (M := M)) :
    (∫⁻ e, scalarRadialOscillation g a e ∂canonicalFrameMeasure g o) =
      ∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
        scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o :=
  lintegral_lintegral_swap
    ((scalarGeodesicOscillation_joint_continuous g a).measurable.comp measurable_swap).aemeasurable

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem scalar_pair_lintegral_le_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M)) :
    (∫⁻ e, ∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)
      ∂volumeMeasure g ∂canonicalFrameMeasure g o) ≤
      riemannianChartFactor * polarAngularMass * ENNReal.ofReal C *
        ∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
          scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o := by
  let D := riemannianChartFactor * polarAngularMass * ENNReal.ofReal C
  have hD : D ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) polarAngularMass_ne_top
    · exact ENNReal.ofReal_ne_top
  have hp (e : FrameBundle g) (he : e ∈ o.positive) :
      (∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2) ∂volumeMeasure g) ≤
      D * ∫⁻ q : Directions,
        scalarRadialOscillation g a
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure := by
    have hW : Measurable (fun y => ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)) := by
      simpa only [Function.comp_apply, Pi.pow_apply, Pi.sub_apply] using!
        (ENNReal.continuous_ofReal.comp
          ((a.property.continuous.sub
            (continuous_const : Continuous (fun _ : M => a.val e.base))).pow 2)).measurable
    have h := volume_lintegral_le_bounded_radial g o hRic hbound e he
      (fun y => ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)) hW
    convert h using 1
    congr 1
    apply lintegral_congr
    intro q
    apply lintegral_congr
    intro r
    rw [frameExponential_direction_ray g o e he q r]
    rfl
  calc
    _ ≤ ∫⁻ e, D * (∫⁻ q : Directions,
        scalarRadialOscillation g a
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure)
          ∂canonicalFrameMeasure g o :=
      lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono hp)
    _ = D * ∫⁻ e, scalarRadialOscillation g a e ∂canonicalFrameMeasure g o := by
      rw [lintegral_const_mul' _ _ hD,
        canonicalFrame_lintegral_sphere_rotations g o _ (scalarRadialOscillation_measurable g a)]
    _ = _ := by rw [scalarRadialOscillation_integral]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the flow translation estimate over the bounded
radial interval gives a global pair-oscillation energy estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarPairEnergy_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalar_radial_lintegral_energy_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    (∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
      scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o) ≤
      ENNReal.ofReal (Real.pi ^ 3 *
        ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) := by
  let A := ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Real.pi) :
      (∫⁻ e, scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o) ≤
        ENNReal.ofReal (Real.pi ^ 2 * A) := by
    refine (scalarGeodesicOscillation_integral_bound g o hRic a r).trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hr.1 Real.pi_pos.le).mpr hr.2) (sq_nonneg _)
  calc
    _ ≤ ∫⁻ _r in Icc (0 : ℝ) Real.pi, ENNReal.ofReal (Real.pi ^ 2 * A) :=
      lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono hpoint)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      congr 1
      ring

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem scalar_pair_lintegral_energy_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M)) :
    (∫⁻ e, ∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)
      ∂volumeMeasure g ∂canonicalFrameMeasure g o) ≤
      riemannianChartFactor * polarAngularMass * ENNReal.ofReal C *
        ENNReal.ofReal (Real.pi ^ 3 *
          ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) :=
  (scalar_pair_lintegral_le_radial g o hRic hbound a).trans
    (mul_le_mul_right (scalar_radial_lintegral_energy_bound g o hRic a) _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalize the geometric pair estimate and express its left side as
the variance of an actual scalar function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

section Probability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [SecondCountableTopology X] [CompactSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem continuous_pairwise_square_lintegral (a : C(X, ℝ)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((a x - a y) ^ 2) ∂μ ∂μ) =
      ENNReal.ofReal (2 * ((∫ x, a x ^ 2 ∂μ) - (∫ x, a x ∂μ) ^ 2)) := by
  have hc : Continuous (fun p : X × X => (a p.1 - a p.2) ^ 2) :=
    ((a.continuous.comp continuous_fst).sub (a.continuous.comp continuous_snd)).pow 2
  have hi := hc.integrable_of_hasCompactSupport (μ := μ.prod μ)
    (HasCompactSupport.of_compactSpace _)
  have hm : Measurable (fun p : X × X => ENNReal.ofReal ((a p.1 - a p.2) ^ 2)) := by
    simpa only [Function.comp_apply] using! (ENNReal.continuous_ofReal.comp hc).measurable
  rw [← lintegral_prod _ hm.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun p => sq_nonneg (a p.1 - a p.2))),
    integral_prod _ hi, continuous_pairwise_square_integral]

end Probability

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance scalarNormalizedPair_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def scalarPairConstant (g : SmoothMetric M) (C : ℝ) : ℝ≥0∞ :=
  (volumeMeasure g univ)⁻¹ * (riemannianChartFactor * polarAngularMass * ENNReal.ofReal C) *
    ENNReal.ofReal (Real.pi ^ 3)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem scalarPairConstant_ne_top (g : SmoothMetric M) (C : ℝ) :
    scalarPairConstant g C ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (actual_finitePositiveVolume g).positive.ne'
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) polarAngularMass_ne_top)
        ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

theorem normalized_scalar_pair_energy_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M)) :
    (∫⁻ e, ∫⁻ f, ENNReal.ofReal ((a.val e.base - a.val f.base) ^ 2)
      ∂canonicalFrameMeasure g o ∂canonicalFrameMeasure g o) ≤
      scalarPairConstant g C *
        ENNReal.ofReal (‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) := by
  let μ := canonicalFrameMeasure g o
  have hp (e : FrameBundle g) :
      (∫⁻ f, ENNReal.ofReal ((a.val e.base - a.val f.base) ^ 2) ∂μ) =
        (volumeMeasure g univ)⁻¹ *
          ∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2) ∂volumeMeasure g := by
    have hm : Measurable (fun y => ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)) := by
      simpa only [Function.comp_apply, Pi.pow_apply, Pi.sub_apply] using!
        (ENNReal.continuous_ofReal.comp ((a.property.continuous.sub
          (continuous_const : Continuous (fun _ : M => a.val e.base))).pow 2)).measurable
    have h := (canonicalFrameMeasure_base g o).lintegral_comp hm
    rw [normalizedVolume, lintegral_smul_measure] at h
    convert h using 1
    apply lintegral_congr
    intro f
    congr 1
    ring
  change (∫⁻ e, ∫⁻ f, ENNReal.ofReal ((a.val e.base - a.val f.base) ^ 2) ∂μ ∂μ) ≤ _
  simp_rw [hp]
  rw [lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.mpr (actual_finitePositiveVolume g).positive.ne')]
  have h := mul_le_mul_right (scalar_pair_lintegral_energy_bound g o hRic hbound a)
    ((volumeMeasure g univ)⁻¹)
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi ^ 3)]
  simp only [scalarPairConstant, mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The geometric pair estimate gives an actual mean-zero Poincaré
inequality for smooth scalars. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance scalarSmoothPoincare_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothScalar_value_norm_sq (g : SmoothMetric M) (o : FrameOrientation g)
    (a : SmoothScalar (M := M)) :
    ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 =
      ∫ e, (a.val e.base) ^ 2 ∂canonicalFrameMeasure g o := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothScalarValue g a))
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothScalarValue g a)) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with e
  change a.val e.base * a.val e.base = (a.val e.base) ^ 2
  ring

theorem smoothScalar_poincare_of_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M))
    (hmean : (∫ e, a.val e.base ∂canonicalFrameMeasure g o) = 0) :
    ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 ≤
      ((scalarPairConstant g C).toReal + 1) *
        ∑ i : Fin 4, ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) i a‖ ^ 2 := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  let V := ‖smoothScalarValueL2 g μ a‖ ^ 2
  let E := ‖smoothScalarGradientL2 d 0 a‖ ^ 2
  have hp := normalized_scalar_pair_energy_bound g o hRic hbound a
  change (∫⁻ e, ∫⁻ f, ENNReal.ofReal
    (((smoothScalarValue g a) e - (smoothScalarValue g a) f) ^ 2) ∂μ ∂μ) ≤ _ at hp
  rw [continuous_pairwise_square_lintegral μ (smoothScalarValue g a)] at hp
  change ENNReal.ofReal (2 * ((∫ e, a.val e.base ^ 2 ∂μ) -
    (∫ e, a.val e.base ∂μ) ^ 2)) ≤ scalarPairConstant g C * ENNReal.ofReal E at hp
  rw [hmean, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    ← smoothScalar_value_norm_sq g o a] at hp
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (scalarPairConstant_ne_top g C) ENNReal.ofReal_ne_top) hp
  change (ENNReal.ofReal (2 * V)).toReal ≤
    (scalarPairConstant g C * ENNReal.ofReal E).toReal at hr
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * V), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ E)] at hr
  have hv : 0 ≤ V := sq_nonneg _
  have he : 0 ≤ E := sq_nonneg _
  have hE : E ≤ ∑ i : Fin 4, ‖smoothScalarGradientL2 d i a‖ ^ 2 := by
    change ‖smoothScalarGradientL2 d 0 a‖ ^ 2 ≤ _
    exact Finset.single_le_sum
      (fun i _ => sq_nonneg ‖smoothScalarGradientL2 d i a‖)
      (Finset.mem_univ (0 : Fin 4))
  have hK : 0 ≤ (scalarPairConstant g C).toReal := ENNReal.toReal_nonneg
  calc
    V ≤ ((scalarPairConstant g C).toReal + 1) * E := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

theorem exists_smoothScalar_poincare_constant (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : SmoothScalar (M := M),
      (∫ e, a.val e.base ∂canonicalFrameMeasure g o) = 0 →
      ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 ≤
        K * ∑ i : Fin 4, ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) i a‖ ^ 2 := by
  obtain ⟨C, _hC, hC⟩ := exists_uniform_actualJacobi_det_bound g hRic
  exact ⟨(scalarPairConstant g C).toReal + 1, by positivity,
    fun a ha => smoothScalar_poincare_of_bound g o hRic hC a ha⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unconditional weak Poisson solvability for the actual metric.  The
Poincaré constant comes from the exponential-map pair estimate.  The value
of the solution is a scalar on the base manifold, and its equation holds
against every element of the actual first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem smoothScalar_centered_orthogonal_one (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarValueL2 g μ (smoothScalarSubtractMean (μ := μ) a))
      (scalarL2One g μ) = 0 := by
  rw [real_inner_comm]
  change scalarH1Mean d (smoothScalarToH1 d (smoothScalarSubtractMean (μ := μ) a)) = 0
  rw [scalarH1Mean_smooth]
  exact smoothScalarSubtractMean_mean_zero d a

/-- A mean-zero source pairs identically with a test and its mean-zero
projection.  Consequently the variational solution tests against all H¹. -/
theorem scalarMeanZeroWeakPoisson_all_tests (d : ParallelMetricData g μ)
    {K : ℝ} (hK : 0 < K) (hP : SmoothScalarPoincare d K)
    (f : ScalarL2 g μ) (hf : inner ℝ f (scalarL2One g μ) = 0)
    (v : scalarH1 d) :
    (∑ i : Fin 4, inner ℝ
      (scalarH1Gradient d i (scalarMeanZeroWeakPoisson d hK hP f).val)
      (scalarH1Gradient d i v)) = inner ℝ f (scalarH1Value d v) := by
  have h := scalarMeanZeroWeakPoisson_weak d hK hP f
    (scalarH1MeanZeroProjection d v)
  change (∑ i : Fin 4, inner ℝ
    (scalarH1Gradient d i (scalarMeanZeroWeakPoisson d hK hP f).val)
    (scalarH1Gradient d i (scalarH1SubtractMean d v))) =
      inner ℝ f (scalarH1Value d (scalarH1SubtractMean d v)) at h
  simpa only [scalarH1Gradient_subtractMean, scalarH1Value_subtractMean,
    inner_sub_right, inner_smul_right, hf, mul_zero, sub_zero] using h

end General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance actualWeakPoisson_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

/-- For every actual smooth source there is a mean-zero weak solution of
Δu = a - average(a), with an actual base L² representative. -/
theorem actual_scalar_weak_poisson (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ u : scalarH1MeanZero (canonicalParallelMetricData g o hRic),
      (∃ b : Lp ℝ 2 (normalizedVolume g),
        scalarBasePullback g o b =
          scalarH1Value (canonicalParallelMetricData g o hRic) u.val) ∧
      ∀ v : scalarH1 (canonicalParallelMetricData g o hRic),
        (∑ i : Fin 4, inner ℝ
          (scalarH1Gradient (canonicalParallelMetricData g o hRic) i u.val)
          (scalarH1Gradient (canonicalParallelMetricData g o hRic) i v)) =
          -(inner ℝ
            (smoothScalarValueL2 g (canonicalFrameMeasure g o)
              (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a))
            (scalarH1Value (canonicalParallelMetricData g o hRic) v)) := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  obtain ⟨K, hK, hP⟩ := exists_smoothScalar_poincare_constant g o hRic
  let f := -(smoothScalarValueL2 g μ (smoothScalarSubtractMean (μ := μ) a))
  have hf : inner ℝ f (scalarL2One g μ) = 0 := by
    dsimp only [f]
    rw [inner_neg_left, smoothScalar_centered_orthogonal_one d a, neg_zero]
  refine ⟨scalarMeanZeroWeakPoisson d hK hP f,
    scalarH1_base_representative g o d _, ?_⟩
  intro v
  simpa only [f, inner_neg_left] using
    scalarMeanZeroWeakPoisson_all_tests d hK hP f hf v

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth representative of a weak scalar Poisson solution satisfies the
pointwise geometric Poisson equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def smoothScalarLaplacian (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    SmoothScalar (M := M) :=
  ⟨scalarLaplacianBase g a, scalarLaplacianBase_smooth g a.property⟩

theorem smoothScalarLaplacian_valueL2 (g : SmoothMetric M)
    (μ : Measure (FrameBundle g)) [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (a : SmoothScalar (M := M)) :
    smoothScalarValueL2 g μ (smoothScalarLaplacian g a) =
      smoothScalarLaplacianL2 (μ := μ) a := by
  change ContinuousMap.toLp 2 μ ℝ (smoothScalarValue g (smoothScalarLaplacian g a)) =
    ContinuousMap.toLp 2 μ ℝ (smoothScalarLaplacianField g a)
  congr 1
  ext e
  exact (scalarLaplacian_eq_base g a e).symm

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarStrong_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarStrong_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem smoothScalarValueL2_injective (g : SmoothMetric M) (o : FrameOrientation g) :
    Function.Injective (smoothScalarValueL2 g (canonicalFrameMeasure g o)) := by
  let := normalizedVolume_isOpenPosMeasure g
  intro a b hab
  have hbase : smoothScalarBaseL2 g a = smoothScalarBaseL2 g b := by
    apply (scalarBasePullback g o).injective
    simpa only [scalarBasePullback_smooth] using hab
  have hc := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)) hbase
  apply Subtype.ext
  exact congrArg DFunLike.coe hc

/-- A smooth representative of the constructed weak solution satisfies the
actual pointwise geometric Poisson equation. -/
theorem scalar_poisson_pointwise_of_smooth_representative (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a φ : SmoothScalar (M := M))
    (u : scalarH1 (canonicalParallelMetricData g o hRic))
    (hu : scalarH1Value (canonicalParallelMetricData g o hRic) u =
      smoothScalarValueL2 g (canonicalFrameMeasure g o) φ)
    (hweak : ∀ v : scalarH1 (canonicalParallelMetricData g o hRic),
      (∑ i : Fin 4, inner ℝ
        (scalarH1Gradient (canonicalParallelMetricData g o hRic) i u)
        (scalarH1Gradient (canonicalParallelMetricData g o hRic) i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o)
          (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a))
          (scalarH1Value (canonicalParallelMetricData g o hRic) v))) :
    ∀ e : FrameBundle g, scalarLaplacian g φ e =
      a.val e.base - ∫ f, a.val f.base ∂canonicalFrameMeasure g o := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  let c := smoothScalarSubtractMean (μ := μ) a
  have hueq : u = smoothScalarToH1 d φ := scalarH1_eq_smooth_of_value d u φ hu
  have ht (b : SmoothScalar (M := M)) :
      inner ℝ (smoothScalarLaplacianL2 (μ := μ) φ - smoothScalarValueL2 g μ c)
        (smoothScalarValueL2 g μ b) = 0 := by
    have hw := hweak (smoothScalarToH1 d b)
    rw [hueq] at hw
    change smoothScalarDirichlet d φ b =
      -(inner ℝ (smoothScalarValueL2 g μ c) (smoothScalarValueL2 g μ b)) at hw
    rw [smoothScalarDirichlet_symm, smoothScalarDirichlet_laplacian_pairing,
      real_inner_comm (smoothScalarLaplacianL2 (μ := μ) φ) (smoothScalarValueL2 g μ b)] at hw
    rw [inner_sub_left]
    linarith
  let r := smoothScalarLaplacian g φ - c
  have hr : smoothScalarValueL2 g μ r =
      smoothScalarLaplacianL2 (μ := μ) φ - smoothScalarValueL2 g μ c := by
    dsimp only [r]
    rw [map_sub, smoothScalarLaplacian_valueL2]
  have hz : smoothScalarValueL2 g μ r = 0 := by
    have h := ht r
    rw [← hr] at h
    exact (inner_self_eq_zero).mp h
  have hr0 : r = 0 := smoothScalarValueL2_injective g o (by simpa only [map_zero] using hz)
  intro e
  have h := congrArg (fun b : SmoothScalar (M := M) => b.val e.base) hr0
  change scalarLaplacianBase g φ e.base -
    (a.val e.base - (∫ f, a.val f.base ∂μ) * 1) = 0 at h
  rw [scalarLaplacian_eq_base]
  dsimp only [μ] at h
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak scalar minimum principle from actual parallel-frame
derivatives. No coordinate ellipticity premise is introduced. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalarGradient_zero_of_local_min (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (e : FrameBundle g) (hmin : IsLocalMin a.val e.base)
    (i : Fin 4) : scalarGradient g a.val e i = 0 := by
  let s := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let φ := d.toMetricGreenData.flow i
  obtain ⟨f, hf⟩ := (φ.map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  have hcurve : Continuous (fun t : ℝ => φ.map t f) :=
    φ.continuous.comp (continuous_id.prodMk continuous_const)
  have hm : IsLocalMin (fun t : ℝ => a.val (φ.map t f).base) 0 := by
    have hbase : IsLocalMin a.val (φ.map 0 f).base := by rw [hf]; exact hmin
    exact IsLocalMin.comp_continuous (g := fun t : ℝ => (φ.map t f).base) (b := 0)
      hbase ((continuous_frameBase g).comp hcurve).continuousAt
  have h := hm.hasDerivAt_eq_zero (s.derivativeValue i 0 f)
  simpa only [hf] using h

theorem scalarLaplacian_nonneg_of_local_min (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (e : FrameBundle g) (hmin : IsLocalMin a.val e.base) :
    0 ≤ scalarLaplacian g a.val e := by
  let s := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  apply Finset.sum_nonneg
  intro i _
  let φ := d.toMetricGreenData.flow i
  obtain ⟨f, hf⟩ := (φ.map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  have hcurve : Continuous (fun t : ℝ => φ.map t f) :=
    φ.continuous.comp (continuous_id.prodMk continuous_const)
  have hm : IsLocalMin (fun t : ℝ => a.val (φ.map t f).base) 0 := by
    have hbase : IsLocalMin a.val (φ.map 0 f).base := by rw [hf]; exact hmin
    exact IsLocalMin.comp_continuous (g := fun t : ℝ => (φ.map t f).base) (b := 0)
      hbase ((continuous_frameBase g).comp hcurve).continuousAt
  have h := scalar_second_derivative_nonneg_at_local_min
    (fun t => s.derivativeValue i t f) (fun t => s.derivativeGradient i i t f)
    ((s.continuousHessian i i).comp hcurve).continuousAt hm
  simpa only [hf] using h

variable [CompactSpace M] [Nonempty M]

/-- A negative minimum contradicts a strictly negative Laplacian there.
This is the comparison step used for a local positive barrier. -/
theorem smoothScalar_nonneg_of_negative_laplacian_on_negative (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M))
    (hstrict : ∀ e : FrameBundle g, a.val e.base < 0 → scalarLaplacian g a.val e < 0) :
    ∀ x, 0 ≤ a.val x := by
  obtain ⟨x₀, _, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    a.property.continuous.continuousOn
  have hm : IsLocalMin a.val x₀ := Filter.Eventually.of_forall (fun x => hx₀ (mem_univ x))
  intro x
  by_contra hn
  have hneg : a.val x₀ < 0 := lt_of_le_of_lt (hx₀ (mem_univ x)) (lt_of_not_ge hn)
  exact (not_lt_of_ge (scalarLaplacian_nonneg_of_local_min d a (frameAt g x₀) hm))
    (hstrict (frameAt g x₀) hneg)

theorem smoothScalar_nonneg_of_shifted_supersolution (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) {c : ℝ} (hc : 0 < c)
    (hineq : ∀ e : FrameBundle g, scalarLaplacian g a.val e ≤ c * a.val e.base) :
    ∀ x, 0 ≤ a.val x := by
  apply smoothScalar_nonneg_of_negative_laplacian_on_negative d a
  intro e he
  exact (hineq e).trans_lt (mul_neg_of_pos_of_neg hc he)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The variational construction gives an actual distributional solution on
the base manifold, tested against its smooth scalar Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance scalarDistribution_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarDistribution_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem actual_scalar_distributional_poisson (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ b : Lp ℝ 2 (normalizedVolume g), ∀ v : SmoothScalar (M := M),
      inner ℝ b (smoothScalarBaseL2 g (smoothScalarLaplacian g v)) =
        inner ℝ (smoothScalarBaseL2 g
          (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a))
          (smoothScalarBaseL2 g v) := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  let c := smoothScalarSubtractMean (μ := μ) a
  obtain ⟨u, ⟨b, hb⟩, hu⟩ := actual_scalar_weak_poisson g o hRic a
  refine ⟨b, ?_⟩
  intro v
  have h := hu (smoothScalarToH1 d v)
  change (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u.val)
    (smoothScalarGradientL2 d i v)) =
      -(inner ℝ (smoothScalarValueL2 g μ c) (smoothScalarValueL2 g μ v)) at h
  have hg := scalarH1_green d u.val v
  have heq : inner ℝ (scalarH1Value d u.val) (smoothScalarLaplacianL2 (μ := μ) v) =
      inner ℝ (smoothScalarValueL2 g μ c) (smoothScalarValueL2 g μ v) := by
    linarith
  calc
    inner ℝ b (smoothScalarBaseL2 g (smoothScalarLaplacian g v)) =
        inner ℝ (scalarBasePullback g o b)
          (scalarBasePullback g o (smoothScalarBaseL2 g (smoothScalarLaplacian g v))) :=
      ((scalarBasePullback g o).inner_map_map _ _).symm
    _ = inner ℝ (scalarH1Value d u.val) (smoothScalarLaplacianL2 (μ := μ) v) := by
      rw [hb, scalarBasePullback_smooth, smoothScalarLaplacian_valueL2]
    _ = inner ℝ (smoothScalarValueL2 g μ c) (smoothScalarValueL2 g μ v) := heq
    _ = inner ℝ (smoothScalarBaseL2 g c) (smoothScalarBaseL2 g v) := by
      rw [← scalarBasePullback_smooth g o c, ← scalarBasePullback_smooth g o v,
        (scalarBasePullback g o).inner_map_map]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The distributional Poisson equation in metric chart measure.
Its coordinate density is derived from Riemannian volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function Filter
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem normalizedVolume_integral_chart (g : SmoothMetric M) (c : M)
    (f : M → ℝ) (hf : ∀ x, x ∉ (chartAt FourSpace c).source → f x = 0) :
    (∫ x, f x ∂normalizedVolume g) =
      (normalizedChartFactor g).toReal *
        ∫ z in (chartAt FourSpace c).target,
          chartVolumeDensity g c z * f ((chartAt FourSpace c).symm z) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf,
    normalizedVolume_restrict_chart, integral_smul_measure]
  have he : MeasurableEmbedding
      (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  rw [he.integral_map]
  have hd : Continuous (fun z : ChartTarget c => chartVolumeDensity g c z.val) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (chartVolumeDensity_contDiffAt g c z z.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hdm : Measurable (fun z : ChartTarget c =>
      ENNReal.ofReal (chartVolumeDensity g c z.val)) := by
    simpa only [Function.comp_def] using (ENNReal.continuous_ofReal.comp hd).measurable
  rw [integral_withDensity_eq_integral_toReal_smul
    hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (le_of_lt (chartVolumeDensity_pos g c _
    (Subtype.property _))), smul_eq_mul]
  congr 1
  exact integral_subtype_comap (chartAt FourSpace c).open_target.measurableSet
    (fun z => chartVolumeDensity g c z * f ((chartAt FourSpace c).symm z))

omit [IsManifold I4 ∞ M] [MeasurableSpace M] [BorelSpace M] in
theorem scalarChartLift_tsupport (c : M) (ψ : FourSpace → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    tsupport (scalarChartLift c ψ) ⊆ (chartAt FourSpace c).source := by
  have hK : IsCompact ((chartAt FourSpace c).symm '' tsupport ψ) :=
    hc.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hs)
  apply (closure_minimal (scalarChartLift_support c ψ) hK.isClosed).trans
  rintro _ ⟨z, hz, rfl⟩
  exact (chartAt FourSpace c).map_target (hs hz)

section Compact

variable [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
  [PreconnectedSpace M]

local instance scalarChartIntegral_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothScalarBaseL2_inner_right (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g)) (v : SmoothScalar (M := M)) :
    inner ℝ b (smoothScalarBaseL2 g v) = ∫ x, b x * v.val x ∂normalizedVolume g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    (⟨v.val, v.property.continuous⟩ : C(M, ℝ))] with x hx
  simp only [smoothScalarBaseL2] at *
  rw [hx, real_inner_comm]
  rfl

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothScalarBaseL2_inner (g : SmoothMetric M)
    (u v : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarBaseL2 g u) (smoothScalarBaseL2 g v) =
      ∫ x, u.val x * v.val x ∂normalizedVolume g := by
  rw [smoothScalarBaseL2_inner_right]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    (⟨u.val, u.property.continuous⟩ : C(M, ℝ))] with x hx
  rw [show smoothScalarBaseL2 g u x = u.val x from hx]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem normalizedChartFactor_toReal_pos (g : SmoothMetric M) :
    0 < (normalizedChartFactor g).toReal := by
  have hV := actual_finitePositiveVolume g
  have hH : 0 < (euclideanHausdorffFactor : ℝ≥0∞) := by
    exact_mod_cast euclideanHausdorffFactor_pos
  apply ENNReal.toReal_pos
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hV.finite.ne)
      (mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hH.ne')
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV.positive.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)

theorem actual_scalar_chart_distribution (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ b : Lp ℝ 2 (normalizedVolume g), ∀ (c : M) (ψ : FourSpace → ℝ)
      (_hψ : ContDiff ℝ ∞ ψ) (_hc : HasCompactSupport ψ)
      (_hs : tsupport ψ ⊆ (chartAt FourSpace c).target),
      (∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (b ((chartAt FourSpace c).symm z) *
          scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z))) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        ((smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a).val
          ((chartAt FourSpace c).symm z) * ψ z) := by
  obtain ⟨b, hb⟩ := actual_scalar_distributional_poisson g o hRic a
  refine ⟨b, ?_⟩
  intro c ψ hψ hc hs
  let v := scalarChartTest c ψ hψ hc hs
  have h := hb v
  rw [smoothScalarBaseL2_inner_right, smoothScalarBaseL2_inner] at h
  have hsupport := scalarChartLift_tsupport c ψ hc hs
  have hleft : ∀ x, x ∉ (chartAt FourSpace c).source →
      b x * scalarLaplacianBase g (scalarChartLift c ψ) x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => hx (hsupport (scalarLaplacianBase_tsupport g _ h))), mul_zero]
  have hright : ∀ x, x ∉ (chartAt FourSpace c).source →
      (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a).val x *
        scalarChartLift c ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport h)), mul_zero]
  change (∫ x, b x * scalarLaplacianBase g (scalarChartLift c ψ) x ∂normalizedVolume g) =
    ∫ x, (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a).val x *
      scalarChartLift c ψ x ∂normalizedVolume g at h
  rw [normalizedVolume_integral_chart g c _ hleft,
    normalizedVolume_integral_chart g c _ hright] at h
  apply (mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne') at h
  convert h using 1
  apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  dsimp only
  rw [scalarChartLift_symm c ψ hz]

end Compact
end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential barrier and its actual metric Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def smoothScalarExponentialBarrier (a : SmoothScalar (M := M)) (k c : ℝ) :
    SmoothScalar (M := M) :=
  smoothScalarCompose (fun r => Real.exp (-k * r) - c)
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).sub contDiff_const) a

theorem smoothScalarExponentialBarrier_gradient (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (k c : ℝ) (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarExponentialBarrier a k c).val e i =
      -k * Real.exp (-k * a.val e.base) * scalarGradient g a.val e i := by
  rw [smoothScalarExponentialBarrier, smoothScalarCompose_gradient d]
  have hd : HasDerivAt (fun r : ℝ => Real.exp (-k * r) - c)
      (Real.exp (-k * a.val e.base) * -k) (a.val e.base) :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (a.val e.base)).const_mul (-k)).exp).sub_const c
  rw [hd.deriv]
  ring

theorem smoothScalarExponentialBarrier_hessian (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (k c : ℝ) (e : FrameBundle g) (i j : Fin 4) :
    scalarHessian g (smoothScalarExponentialBarrier a k c).val e i j =
      Real.exp (-k * a.val e.base) *
        (k ^ 2 * scalarGradient g a.val e i * scalarGradient g a.val e j -
          k * scalarHessian g a.val e i j) := by
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let b := smoothScalarExponentialBarrier a k c
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  have h := sb.derivativeGradient i j 0 f
  have h' := (((sa.derivativeValue i 0 f).const_mul (-k)).exp.const_mul (-k)).mul
    (sa.derivativeGradient i j 0 f)
  have heq : (fun t => scalarGradient g b.val ((d.toMetricGreenData.flow i).map t f) j) =
      (fun t => -k * Real.exp (-k * a.val ((d.toMetricGreenData.flow i).map t f).base) *
        scalarGradient g a.val ((d.toMetricGreenData.flow i).map t f) j) :=
    funext (fun t => smoothScalarExponentialBarrier_gradient d a k c _ j)
  rw [heq] at h
  have hu := h.unique h'
  rw [hf] at hu
  change scalarHessian g (smoothScalarExponentialBarrier a k c).val e i j = _ at hu
  rw [hu]
  ring

theorem smoothScalarExponentialBarrier_laplacian (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (k c : ℝ) (e : FrameBundle g) :
    scalarLaplacian g (smoothScalarExponentialBarrier a k c).val e =
      Real.exp (-k * a.val e.base) *
        (k ^ 2 * (∑ i, scalarGradient g a.val e i ^ 2) - k * scalarLaplacian g a.val e) := by
  simp only [scalarLaplacian, smoothScalarExponentialBarrier_hessian d]
  calc
    _ = Real.exp (-k * a.val e.base) *
        (∑ i, (k ^ 2 * scalarGradient g a.val e i ^ 2 - k * scalarHessian g a.val e i i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The comparison step for a positive scalar barrier, using the actual
frame Laplacian and the compact minimum principle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalarHessian_sub_smul (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) (ε : ℝ) (e : FrameBundle g) (i j : Fin 4) :
    scalarHessian g (a - ε • b).val e i j =
      scalarHessian g a.val e i j - ε * scalarHessian g b.val e i j := by
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  let sv := Classical.choice (d.scalarCalculus.toPetersenInput
    (a - ε • b).val (a - ε • b).property)
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  have h := sv.derivativeGradient i j 0 f
  have h' := (sa.derivativeGradient i j 0 f).sub ((sb.derivativeGradient i j 0 f).const_mul ε)
  have hgrad (z : FrameBundle g) : scalarGradient g (a - ε • b).val z j =
      scalarGradient g a.val z j - ε * scalarGradient g b.val z j := by
    change (smoothScalarGradient d j (a - ε • b)) z = _
    rw [map_sub, map_smul]
    rfl
  have heq : (fun t => scalarGradient g (a - ε • b).val
      ((d.toMetricGreenData.flow i).map t f) j) =
      fun t => scalarGradient g a.val ((d.toMetricGreenData.flow i).map t f) j -
        ε * scalarGradient g b.val ((d.toMetricGreenData.flow i).map t f) j :=
    funext (fun t => hgrad _)
  rw [heq] at h
  simpa only [hf] using h.unique h'

theorem scalarLaplacian_sub_smul (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) (ε : ℝ) (e : FrameBundle g) :
    scalarLaplacian g (a - ε • b).val e =
      scalarLaplacian g a.val e - ε * scalarLaplacian g b.val e := by
  simp only [scalarLaplacian, scalarHessian_sub_smul d,
    Finset.sum_sub_distrib, Finset.mul_sum]

variable [CompactSpace M] [Nonempty M]

theorem scalar_barrier_comparison (d : ParallelMetricData g μ)
    (u b : SmoothScalar (M := M)) {ε c₀ : ℝ} (hε : 0 < ε) (hc₀ : 0 ≤ c₀)
    (hu : ∀ e : FrameBundle g, scalarLaplacian g u.val e ≤ c₀ * u.val e.base)
    (hb : ∀ e : FrameBundle g, u.val e.base < ε * b.val e.base →
      c₀ * b.val e.base < scalarLaplacian g b.val e) :
    ∀ x, ε * b.val x ≤ u.val x := by
  have hnonneg : ∀ x, 0 ≤ (u - ε • b).val x := by
    apply smoothScalar_nonneg_of_negative_laplacian_on_negative d
    intro e he
    change u.val e.base - ε * b.val e.base < 0 at he
    have hbar := mul_lt_mul_of_pos_left (hb e (sub_neg.mp he)) hε
    rw [scalarLaplacian_sub_smul d]
    calc
      _ ≤ c₀ * u.val e.base - ε * scalarLaplacian g b.val e := sub_le_sub_right (hu e) _
      _ < c₀ * u.val e.base - ε * (c₀ * b.val e.base) := sub_lt_sub_left hbar _
      _ = c₀ * (u.val e.base - ε * b.val e.base) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc₀ he.le
  intro x
  exact sub_nonneg.mp (hnonneg x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Choice and verification of the large parameter in the exponential
barrier on an annulus where the radial differential does not vanish. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem scalar_barrier_parameter {η B c₀ : ℝ} (hη : 0 < η)
    (hB : 0 ≤ B) (hc₀ : 0 ≤ c₀) : ∃ k : ℝ, 0 < k ∧ c₀ < k ^ 2 * η - k * B := by
  let k := (B + c₀ + 1) / η + 1
  have hk : 1 < k := by
    dsimp [k]
    have hdiv : 0 < (B + c₀ + 1) / η := div_pos (by linarith) hη
    linarith
  have hmul : k * η = B + c₀ + 1 + η := by
    dsimp [k]
    field_simp [ne_of_gt hη]
  refine ⟨k, lt_trans zero_lt_one hk, ?_⟩
  have hpos : 0 < c₀ + 1 + η := by linarith
  have hprod := mul_lt_mul_of_pos_right hk hpos
  have heq : k ^ 2 * η - k * B = k * (c₀ + 1 + η) := by
    calc
      _ = k * (k * η - B) := by ring
      _ = _ := by rw [hmul]; ring
  rw [heq]
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalar_exponential_barrier_strict (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) {k c η B c₀ : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hc₀ : 0 ≤ c₀) (e : FrameBundle g)
    (hgrad : η ≤ ∑ i, scalarGradient g a.val e i ^ 2)
    (hlap : scalarLaplacian g a.val e ≤ B)
    (hlarge : c₀ < k ^ 2 * η - k * B) :
    c₀ * (smoothScalarExponentialBarrier a k c).val e.base <
      scalarLaplacian g (smoothScalarExponentialBarrier a k c).val e := by
  have hQ := mul_le_mul_of_nonneg_left hgrad (sq_nonneg k)
  have hD := mul_le_mul_of_nonneg_left hlap hk
  have hinside : c₀ < k ^ 2 * (∑ i, scalarGradient g a.val e i ^ 2) -
      k * scalarLaplacian g a.val e :=
    hlarge.trans_le (sub_le_sub hQ hD)
  rw [smoothScalarExponentialBarrier_laplacian d]
  change c₀ * (Real.exp (-k * a.val e.base) - c) < _
  calc
    _ ≤ c₀ * Real.exp (-k * a.val e.base) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hc) hc₀
    _ = Real.exp (-k * a.val e.base) * c₀ := mul_comm _ _
    _ < _ := mul_lt_mul_of_pos_left hinside (Real.exp_pos _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Base L² scalars are locally Euclidean L² in every metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalarChartL2_weighted (g : SmoothMetric M) (c : M)
    (b : Lp ℝ 2 (normalizedVolume g)) :
    MemLp (fun z : ChartTarget c => b ((chartAt FourSpace c).symm z.val)) 2
      ((chartCoordinateMeasure c).withDensity
        (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  have hb := (Lp.memLp b).restrict (chartAt FourSpace c).source
  rw [normalizedVolume_restrict_chart] at hb
  obtain ⟨hF₀, hFtop⟩ := ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)
  have hb' := hb.smul_measure (c := (normalizedChartFactor g)⁻¹)
    (ENNReal.inv_ne_top.mpr hF₀.ne')
  rw [smul_smul, ENNReal.inv_mul_cancel hF₀.ne' hFtop.ne, one_smul] at hb'
  have he : MeasurableEmbedding
      (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  exact he.memLp_map_measure_iff.mp hb'

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem scalarChart_density_lower_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ chartVolumeDensity g c z :=
  hK.exists_forall_le'
    (fun z hz => (chartVolumeDensity_contDiffAt g c z (hKt hz)).continuousAt.continuousWithinAt)
    (fun z hz => chartVolumeDensity_pos g c z (hKt hz))

theorem scalarChartL2_compact (g : SmoothMetric M) (c : M)
    (b : Lp ℝ 2 (normalizedVolume g)) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    MemLp (fun z : FourSpace => b ((chartAt FourSpace c).symm z)) 2
      (volume.restrict K) := by
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let S : Set (ChartTarget c) := Subtype.val ⁻¹' K
  have hS : MeasurableSet S := measurable_subtype_coe hK.isClosed.measurableSet
  obtain ⟨δ, hδ, hδK⟩ := scalarChart_density_lower_bound g c hK hKt
  let d := ENNReal.ofReal δ
  have hd₀ : d ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hdtop : d ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hmeasure : d • μ.restrict S ≤ (μ.withDensity ρ).restrict S := by
    rw [← withDensity_const, restrict_withDensity hS]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with z hz
    exact ENNReal.ofReal_le_ofReal (hδK z.val hz)
  have hdom : μ.restrict S ≤ d⁻¹ • μ.withDensity ρ := by
    calc
      μ.restrict S = d⁻¹ • (d • μ.restrict S) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hd₀ hdtop, one_smul]
      _ ≤ d⁻¹ • (μ.withDensity ρ).restrict S := smul_le_smul_left _ hmeasure
      _ ≤ d⁻¹ • μ.withDensity ρ := by
        gcongr
        exact Measure.restrict_le_self
  have hb : MemLp (fun z : ChartTarget c => b ((chartAt FourSpace c).symm z.val)) 2
      (μ.restrict S) :=
    (scalarChartL2_weighted g c b).of_measure_le_smul (ENNReal.inv_ne_top.mpr hd₀) hdom
  have he := MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet
  have hmap : Measure.map (Subtype.val : ChartTarget c → FourSpace) (μ.restrict S) =
      volume.restrict K := by
    rw [← he.restrict_map]
    change (Measure.map Subtype.val (Measure.comap Subtype.val volume)).restrict K = _
    rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet,
      inter_eq_left.mpr hKt]
  rw [← hmap]
  exact he.memLp_map_measure_iff.mpr hb

theorem scalarChartL2_cutoff (g : SmoothMetric M) (c : M)
    (b : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target) :
    MemLp (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) 2 volume := by
  have hb := scalarChartL2_compact g c b hc hs
  obtain ⟨C, hC⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  have hprod : MemLp (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) 2
      (volume.restrict (tsupport χ)) := by
    apply hb.of_le_mul (c := C) (hχ.aestronglyMeasurable.mul hb.aestronglyMeasurable)
    filter_upwards with z
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC (χ z) (mem_range_self z)) (norm_nonneg _)
  have heq : (tsupport χ).indicator
      (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) =
      (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) := by
    apply indicator_eq_self.2
    intro z hz
    exact (subset_tsupport χ) (left_ne_zero_of_mul hz)
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport χ).measurableSet).mpr hprod

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate test equation for the actual second-order elliptic operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarChartOperator (g : SmoothMetric M) (c : M) (ψ : FourSpace → ℝ)
    (z : FourSpace) : ℝ :=
  ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
    (partialDeriv (fun w => partialDeriv ψ j w) i z -
      ∑ k, christoffel g c z k i j * partialDeriv ψ k z)

theorem scalarChartOperator_congr_nhds (g : SmoothMetric M) (c : M)
    {ψ χ : FourSpace → ℝ} {z : FourSpace} (h : ψ =ᶠ[𝓝 z] χ) :
    scalarChartOperator g c ψ z = scalarChartOperator g c χ z := by
  have h₁ (i : Fin 4) :
      (fun w => partialDeriv ψ i w) =ᶠ[𝓝 z] (fun w => partialDeriv χ i w) :=
    (h.fderiv (𝕜 := ℝ)).mono (fun _ hw =>
      congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hw)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  · exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      ((h₁ j).fderiv_eq (𝕜 := ℝ))
  · apply Finset.sum_congr rfl
    intro k _
    rw [(h₁ k).eq_of_nhds]

theorem scalarChartTest_laplacian [T2Space M] (g : SmoothMetric M)
    (c : M) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z) =
      scalarChartOperator g c ψ z := by
  rw [← chartScalarLaplacian_eq_base g (scalarChartLift_smooth c ψ hψ hc hs) c ⟨z, hz⟩,
    chartScalarLaplacian_coefficients g _ c z hz]
  change scalarChartOperator g c
    (fun w => scalarChartLift c ψ ((chartAt FourSpace c).symm w)) z = _
  apply scalarChartOperator_congr_nhds
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact scalarChartLift_symm c ψ hw

theorem actual_scalar_coordinate_distribution [T3Space M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
    [PreconnectedSpace M] (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ b : Lp ℝ 2 (normalizedVolume g), ∀ (c : M) (ψ : FourSpace → ℝ)
      (_hψ : ContDiff ℝ ∞ ψ) (_hc : HasCompactSupport ψ)
      (_hs : tsupport ψ ⊆ (chartAt FourSpace c).target),
      (∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (b ((chartAt FourSpace c).symm z) * scalarChartOperator g c ψ z)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        ((smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a).val
          ((chartAt FourSpace c).symm z) * ψ z) := by
  obtain ⟨b, hb⟩ := actual_scalar_chart_distribution g o hRic a
  refine ⟨b, ?_⟩
  intro c ψ hψ hc hs
  rw [← hb c ψ hψ hc hs]
  apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  dsimp only
  rw [scalarChartTest_laplacian g c ψ hψ hc hs z hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second coordinate derivatives under a fixed affine change of
four-dimensional coordinates, used for rescaling the actual scalar operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff BigOperators

noncomputable section

def scalarAffineMap (C : Mat4) (q : FourSpace) (z : FourSpace) : FourSpace :=
  (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C z + q

theorem scalarAffineMap_hasFDerivAt (C : Mat4) (q z : FourSpace) :
    HasFDerivAt (scalarAffineMap C q)
      ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C) z := by
  exact ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C).hasFDerivAt.add_const q

theorem scalarAffineMap_jacobian (C : Mat4) (q z : FourSpace) :
    jacobianMatrix (scalarAffineMap C q) z = C := by
  ext a i
  change ((fderiv ℝ (scalarAffineMap C q) z) (coordinateVector i)) a = C a i
  rw [(scalarAffineMap_hasFDerivAt C q z).fderiv]
  change (C *ᵥ WithLp.ofLp (coordinateVector i)) a = _
  simp [coordinateVector, Matrix.mulVec, dotProduct, PiLp.single_apply]

theorem scalarAffineMap_partial (C : Mat4) (q z : FourSpace) (ψ : FourSpace → ℝ)
    (hψ : DifferentiableAt ℝ ψ (scalarAffineMap C q z)) (i : Fin 4) :
    partialDeriv (fun w => ψ (scalarAffineMap C q w)) i z =
      ∑ a, C a i * partialDeriv ψ a (scalarAffineMap C q z) := by
  rw [partialDeriv_comp (scalarAffineMap_hasFDerivAt C q z).differentiableAt hψ,
    scalarAffineMap_jacobian]

theorem scalarAffineMap_partial_second (C : Mat4) (q z : FourSpace)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (i j : Fin 4) :
    partialDeriv (fun w => partialDeriv (fun v => ψ (scalarAffineMap C q v)) j w) i z =
      ∑ a, ∑ b, C a j * (C b i *
        partialDeriv (fun v => partialDeriv ψ a v) b (scalarAffineMap C q z)) := by
  have hp (a : Fin 4) : ContDiff ℝ ∞ (fun w => partialDeriv ψ a w) :=
    (hψ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector a))
  have hfirst : (fun w => partialDeriv (fun v => ψ (scalarAffineMap C q v)) j w) =
      (fun w => ∑ a, C a j * partialDeriv ψ a (scalarAffineMap C q w)) := by
    funext w
    exact scalarAffineMap_partial C q w ψ (hψ.differentiable (by simp) _) j
  rw [hfirst]
  have hd (a : Fin 4) : DifferentiableAt ℝ
      (fun w => C a j * partialDeriv ψ a (scalarAffineMap C q w)) z :=
    ((hp a).differentiable (by simp) _).comp z
      (scalarAffineMap_hasFDerivAt C q z).differentiableAt |>.const_mul (C a j)
  change (fderiv ℝ (fun w => ∑ a, C a j * partialDeriv ψ a (scalarAffineMap C q w)) z)
    (coordinateVector i) = _
  rw [fderiv_fun_sum (fun a (_ : a ∈ Finset.univ) => hd a), _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  change partialDeriv (fun w => C a j * partialDeriv ψ a (scalarAffineMap C q w)) i z = _
  have hmul : partialDeriv (fun w => C a j * partialDeriv ψ a (scalarAffineMap C q w)) i z =
      C a j * partialDeriv (fun w => partialDeriv ψ a (scalarAffineMap C q w)) i z := by
    change (fderiv ℝ ((C a j) • fun w => partialDeriv ψ a (scalarAffineMap C q w)) z)
      (coordinateVector i) = _
    rw [fderiv_const_smul_field]
    rfl
  rw [hmul, scalarAffineMap_partial C q z _ ((hp a).differentiable (by simp) _) i,
    Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual metric coefficients put the chart Laplacian in divergence
form.  This supplies the coefficient identity for local energy estimates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem partialDeriv_chartVolumeDensity (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    partialDeriv (chartVolumeDensity g c) i z =
      (∑ k, christoffel g c z k i k) * chartVolumeDensity g c z := by
  let x : ℝ → FourSpace := fun t => z + t • coordinateVector i
  have hx : HasDerivAt x (coordinateVector i) 0 := by
    simpa only [x, one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add z
  have hz₀ : x 0 = z := by simp [x]
  have h₁ := hasDerivAt_chartVolumeDensity g c x (fun r => coordinateVector i r)
    0 (hz₀.symm ▸ hz) (by simpa using hx)
  have h₂ := (chartVolumeDensity_contDiffAt g c z hz).differentiableAt (by simp)
  have h₃ := hasDerivAt_coordinate_comp hx (hz₀.symm ▸ h₂)
  have he := h₃.unique h₁
  simpa [hz₀, coordinateVector, PiLp.single_apply,
    connectionMatrix, Matrix.trace, Matrix.sum_apply, Matrix.smul_apply] using he

private theorem scalar_metric_trace_cancellation (H : Mat4)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hΓ : ∀ a i k, Γ a i k = Γ a k i) (j : Fin 4) :
    (∑ i, (∑ k, Γ k i k) * H i j) =
      ∑ i, ∑ k, Γ i i k * H k j := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [hΓ k i k]

private theorem scalar_metric_divergence_algebra (ρ : ℝ) (H : Mat4)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hΓ : ∀ a i k, Γ a i k = Γ a k i) (j : Fin 4) :
    (∑ i, ((∑ k, Γ k i k) * ρ * H i j +
      ρ * (-(∑ k, Γ i i k * H k j) - ∑ k, H i k * Γ j i k))) =
      -ρ * ∑ i, ∑ k, H i k * Γ j i k := by
  calc
    _ = ∑ i, (ρ * ((∑ k, Γ k i k) * H i j) -
        ρ * (∑ k, Γ i i k * H k j) - ρ * (∑ k, H i k * Γ j i k)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ρ * ((∑ i, (∑ k, Γ k i k) * H i j) -
        (∑ i, ∑ k, Γ i i k * H k j) - (∑ i, ∑ k, H i k * Γ j i k)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = _ := by rw [scalar_metric_trace_cancellation H Γ hΓ j]; ring

theorem scalar_metric_coefficient_divergence (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    (∑ i, partialDeriv
      (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z) =
      -chartVolumeDensity g c z *
        ∑ i, ∑ k, (metricInChart g c z)⁻¹ i k * christoffel g c z j i k := by
  have hterm (i : Fin 4) :
      partialDeriv (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z =
        (∑ k, christoffel g c z k i k) * chartVolumeDensity g c z *
          (metricInChart g c z)⁻¹ i j + chartVolumeDensity g c z *
            (-(∑ k, christoffel g c z i i k * (metricInChart g c z)⁻¹ k j) -
              ∑ k, (metricInChart g c z)⁻¹ i k * christoffel g c z j i k) := by
    have hρ := (chartVolumeDensity_contDiffAt g c z hz).differentiableAt (by simp)
    have hH := (scalarPrincipalCoefficients_smooth g c z hz i j).differentiableAt (by simp)
    have hprod : partialDeriv
        (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z =
        partialDeriv (chartVolumeDensity g c) i z * (metricInChart g c z)⁻¹ i j +
          chartVolumeDensity g c z * partialDeriv (fun w => (metricInChart g c w)⁻¹ i j) i z := by
      simp only [partialDeriv, fderiv_fun_mul hρ hH, _root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      ring
    rw [hprod, partialDeriv_chartVolumeDensity g c z hz i]
    have hInv := congrFun (congrFun (matrixPartial_inverseMetric g c z hz i) i) j
    change partialDeriv (fun w => (metricInChart g c w)⁻¹ i j) i z = _ at hInv
    rw [hInv]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.transpose_apply, connectionMatrix]
  simp_rw [hterm]
  exact scalar_metric_divergence_algebra _ _ _ (christoffel_comm g c z) j

private theorem scalar_divergence_expansion (ρ : ℝ) (H D Q : Fin 4 → Fin 4 → ℝ)
    (P : Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hD : ∀ j, (∑ i, D i j) = -ρ * ∑ i, ∑ k, H i k * Γ j i k) :
    (∑ i, ∑ j, (D i j * P j + ρ * H i j * Q i j)) =
      ρ * ∑ i, ∑ j, H i j * (Q i j - ∑ k, Γ k i j * P k) := by
  have ht : (∑ j, (∑ i, ∑ k, H i k * Γ j i k) * P j) =
      ∑ i, ∑ k, H i k * (∑ j, Γ j i k * P j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hd : (∑ i, ∑ j, D i j * P j) =
      -ρ * ∑ i, ∑ j, H i j * (∑ k, Γ k i j * P k) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hD]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ht]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hd]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

private theorem scalar_partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem scalarChartOperator_divergence (g : SmoothMetric M) (c : M)
    (ψ : FourSpace → ℝ) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hψ : ContDiffAt ℝ ∞ ψ z) :
    (∑ i, partialDeriv (fun w => ∑ j,
      chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z) =
      chartVolumeDensity g c z * scalarChartOperator g c ψ z := by
  have hP (j : Fin 4) : DifferentiableAt ℝ (fun w => partialDeriv ψ j w) z :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := coordinateVector j))).differentiableAt (by simp)
  have hA (i j : Fin 4) : DifferentiableAt ℝ
      (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) z :=
    ((chartVolumeDensity_contDiffAt g c z hz).mul
      (scalarPrincipalCoefficients_smooth g c z hz i j)).differentiableAt (by simp)
  have hterm (i : Fin 4) :
      partialDeriv (fun w => ∑ j,
        chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z =
      ∑ j, (partialDeriv
        (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z *
          partialDeriv ψ j z + chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j *
            partialDeriv (fun w => partialDeriv ψ j w) i z) := by
    have hs := fderiv_fun_sum (u := Finset.univ)
      (A := fun j w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j *
        partialDeriv ψ j w) (fun j _ => (hA i j).mul (hP j))
    change (fderiv ℝ _ z) (coordinateVector i) = _
    rw [hs, _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact scalar_partial_mul (hA i j) (hP j) i
  simp_rw [hterm]
  exact scalar_divergence_expansion _ _ _ _ _ _
    (scalar_metric_coefficient_divergence g c z hz)

theorem actual_scalar_divergence_distribution [T3Space M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
    [PreconnectedSpace M] (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ b : Lp ℝ 2 (normalizedVolume g), ∀ (c : M) (ψ : FourSpace → ℝ)
      (_hψ : ContDiff ℝ ∞ ψ) (_hc : HasCompactSupport ψ)
      (_hs : tsupport ψ ⊆ (chartAt FourSpace c).target),
      (∫ z in (chartAt FourSpace c).target, b ((chartAt FourSpace c).symm z) *
        ∑ i, partialDeriv (fun w => ∑ j,
          chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        ((smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a).val
          ((chartAt FourSpace c).symm z) * ψ z) := by
  obtain ⟨b, hb⟩ := actual_scalar_coordinate_distribution g o hRic a
  refine ⟨b, ?_⟩
  intro c ψ hψ hc hs
  rw [← hb c ψ hψ hc hs]
  apply MeasureTheory.setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  dsimp only
  rw [scalarChartOperator_divergence g c ψ z hz hψ.contDiffAt]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar energy controls coordinate derivatives in a chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarGradient_chart (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : ChartTarget c) (i : Fin 4) :
    scalarGradient g a (chartGramSection g c 1 (by simp) z) i =
      ∑ j, chartGramMatrix g c 1 z j i *
        partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) j z := by
  have hc := iteratedScalarDerivative_transition g ha c ((chartAt FourSpace c).symm z)
    1 z z.property (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  have h : frameTensor (chartGramMatrix g c 1 z)
      (iteratedScalarDerivative g a c 1 z) ![i] =
      scalarGradient g a (chartGramSection g c 1 (by simp) z) i := by
    rw [hc, ← frameTensor_mul]
    rfl
  rw [← h]
  change frameTensor (chartGramMatrix g c 1 z) (iteratedScalarDerivative g a c 1 z)
    (Fin.cons i (fun k : Fin 0 => Fin.elim0 k)) = _
  rw [frameTensor_cons]
  apply Finset.sum_congr rfl
  intro j _
  rw [frameTensor_zero]
  congr 1
  exact scalarCoordinate_gradient g a c z j

private theorem scalar_covector_bound (E G : Mat4)
    (hE : IsUnit E.det) (hG : Eᵀ * G * E = 1)
    (p : Fin 4 → ℝ) (i : Fin 4) :
    p i ^ 2 ≤ G i i * ∑ j, (∑ k, E k j * p k) ^ 2 := by
  let H := E⁻¹
  let q := Eᵀ *ᵥ p
  have hp : Hᵀ *ᵥ q = p := by
    dsimp only [H, q]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv E hE, Matrix.transpose_one, Matrix.one_mulVec]
  have hmetric : Hᵀ * H = G := by
    have h := congrArg (fun B : Mat4 => Hᵀ * B * H) hG
    have hEH : E * H = 1 := Matrix.mul_nonsing_inv E hE
    calc
      Hᵀ * H = Hᵀ * 1 * H := by simp
      _ = Hᵀ * (Eᵀ * G * E) * H := h.symm
      _ = (E * H)ᵀ * G * (E * H) := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = G := by rw [hEH, Matrix.transpose_one]; simp
  have hnorm : ∑ j, H j i ^ 2 = G i i := by
    have h := congrFun (congrFun hmetric i) i
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have hpi : (∑ j, H j i * q j) = p i := congrFun hp i
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => H j i) q
  rw [hpi, hnorm] at h
  exact h

theorem scalarCoordinate_gradient_sq_le (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : ChartTarget c) (i : Fin 4) :
    (partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z) ^ 2 ≤
      metricInChart g c z i i * scalarDirichletDensity g a ((chartAt FourSpace c).symm z) := by
  let E := chartGramMatrix g c 1 z
  have hE : IsUnit E.det := by
    apply isUnit_iff_ne_zero.mpr
    intro he
    have hn := congrArg Matrix.det (chartGramMatrix_normalizes g c 1 (by simp) z)
    rw [Matrix.det_one] at hn
    change (Eᵀ * metricInChart g c z * E).det = 1 at hn
    simp only [Matrix.det_mul, Matrix.det_transpose, he, zero_mul, mul_zero] at hn
    exact zero_ne_one hn
  have h := scalar_covector_bound E (metricInChart g c z) hE
    (chartGramMatrix_normalizes g c 1 (by simp) z)
    (fun j => partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) j z) i
  have henergy := scalarDirichletDensity_eq_frame g a (chartGramSection g c 1 (by simp) z)
  simp_rw [scalarGradient_chart g ha c z] at henergy
  change scalarDirichletDensity g a ((chartAt FourSpace c).symm z) = _ at henergy
  rwa [← henergy] at h

theorem scalarCoordinate_gradient_sq_le_on_compact (g : SmoothMetric M)
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : M → ℝ), ContMDiff I4 𝓘(ℝ, ℝ) ∞ a →
      ∀ z ∈ K, (partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z) ^ 2 ≤
        C * scalarDirichletDensity g a ((chartAt FourSpace c).symm z) := by
  have hG : ContinuousOn (fun z => metricInChart g c z i i) K :=
    fun z hz => (metricInChart_contDiffAt g c z (hKt hz) i i).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hG).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro a ha z hz
  have hbound : metricInChart g c z i i ≤ max C 0 := by
    calc
      _ ≤ ‖metricInChart g c z i i‖ := le_abs_self _
      _ ≤ C := hC _ ⟨z, hz, rfl⟩
      _ ≤ max C 0 := le_max_left _ _
  exact (scalarCoordinate_gradient_sq_le g ha c ⟨z, hKt hz⟩ i).trans
    (mul_le_mul_of_nonneg_right hbound (scalarDirichletDensity_nonneg g a _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate equation for the same H¹ solution supplied by the
variational solver. This keeps its weak coordinate derivatives and its
distributional Poisson equation attached to one representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance h1Equation_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance h1Equation_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem scalarH1_weak_base_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v))) (v : SmoothScalar (M := M)) :
    inner ℝ (scalarH1BaseValue g o d u) (smoothScalarBaseL2 g (smoothScalarLaplacian g v)) =
      inner ℝ (smoothScalarBaseL2 g f) (smoothScalarBaseL2 g v) := by
  have h := hw (smoothScalarToH1 d v)
  change (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u)
    (smoothScalarGradientL2 d i v)) =
      -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v)) at h
  have hg := scalarH1_green d u v
  have he : inner ℝ (scalarH1Value d u)
      (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) =
      inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v) := by linarith
  calc
    _ = inner ℝ (scalarBasePullback g o (scalarH1BaseValue g o d u))
        (scalarBasePullback g o (smoothScalarBaseL2 g (smoothScalarLaplacian g v))) :=
      ((scalarBasePullback g o).inner_map_map _ _).symm
    _ = inner ℝ (scalarH1Value d u)
        (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) := by
      rw [scalarH1BaseValue_spec, scalarBasePullback_smooth, smoothScalarLaplacian_valueL2]
    _ = _ := by
      rw [he, ← scalarBasePullback_smooth g o f, ← scalarBasePullback_smooth g o v,
        (scalarBasePullback g o).inner_map_map]

theorem scalarH1_weak_coordinate_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v)))
    (c : M) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    (∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
      (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
        scalarChartOperator g c ψ z)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (f.val ((chartAt FourSpace c).symm z) * ψ z) := by
  let b := scalarH1BaseValue g o d u
  have h := scalarH1_weak_base_distribution g o d f u hw (scalarChartTest c ψ hψ hc hs)
  rw [smoothScalarBaseL2_inner_right, smoothScalarBaseL2_inner] at h
  have hsupport := scalarChartLift_tsupport c ψ hc hs
  have hleft : ∀ x, x ∉ (chartAt FourSpace c).source →
      b x * scalarLaplacianBase g (scalarChartLift c ψ) x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsupport (scalarLaplacianBase_tsupport g _ ht))), mul_zero]
  have hright : ∀ x, x ∉ (chartAt FourSpace c).source →
      f.val x * scalarChartLift c ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupport ht)), mul_zero]
  change (∫ x, b x * scalarLaplacianBase g (scalarChartLift c ψ) x ∂normalizedVolume g) =
    ∫ x, f.val x * scalarChartLift c ψ x ∂normalizedVolume g at h
  rw [normalizedVolume_integral_chart g c _ hleft,
    normalizedVolume_integral_chart g c _ hright] at h
  apply (mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne') at h
  calc
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (b ((chartAt FourSpace c).symm z) *
          scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z)) := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartTest_laplacian g c ψ hψ hc hs z hz]
    _ = _ := h
    _ = _ := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartLift_symm c ψ hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pull almost-everywhere identities of the actual volume into a chart.
The strict positivity of the constructed metric density is used explicitly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalar_inverse_chart_ae_predicate (g : SmoothMetric M) (c : M)
    (P : M → Prop) (hP : ∀ᵐ x ∂normalizedVolume g, P x) :
    ∀ᵐ z ∂(volume : Measure FourSpace).restrict (chartAt FourSpace c).target,
      P ((chartAt FourSpace c).symm z) := by
  let e := chartAt FourSpace c
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let φ : ChartTarget c → M := fun z => e.symm z.val
  have he : MeasurableEmbedding φ := e.symm.isOpenEmbedding_restrict.measurableEmbedding
  have hsource := ae_restrict_of_ae hP (s := e.source)
  rw [normalizedVolume_restrict_chart g c] at hsource
  have hfactor : normalizedChartFactor g ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)).1.ne'
  have hm : ∀ᵐ x ∂Measure.map φ (μ.withDensity ρ), P x :=
    (Measure.ae_ennreal_smul_measure_iff hfactor).mp hsource
  have hw : ∀ᵐ z ∂μ.withDensity ρ, P (φ z) := he.ae_map_iff.mp hm
  have hd : Measurable ρ := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (chartVolumeDensity_contDiffAt g c z z.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hsub : ∀ᵐ z ∂μ, P (φ z) := by
    filter_upwards [(ae_withDensity_iff hd).mp hw] with z hz
    exact hz (ENNReal.ofReal_pos.mpr (chartVolumeDensity_pos g c z z.property)).ne'
  exact (ae_restrict_iff_subtype e.open_target.measurableSet).mpr hsub

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine smooth global radial function that agrees with squared
Euclidean chart distance on the inner ball. Outside that ball its value
stays above the inner squared radius, so it can localize a Hopf barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

private def scalarRadialChartCorrection (y : FourSpace) (χ : ContDiffBump y) : FourSpace → ℝ :=
  fun z => χ z * (‖z - y‖ ^ 2 - χ.rOut ^ 2)

private theorem scalarRadialChartCorrection_smooth (y : FourSpace) (χ : ContDiffBump y) :
    ContDiff ℝ ∞ (scalarRadialChartCorrection y χ) := by
  have h : ContDiff ℝ ∞ (fun z : FourSpace => z - y) :=
    contDiff_id.sub contDiff_const
  exact χ.contDiff.mul ((h.norm_sq ℝ).sub contDiff_const)

private theorem scalarRadialChartCorrection_compact (y : FourSpace) (χ : ContDiffBump y) :
    HasCompactSupport (scalarRadialChartCorrection y χ) := χ.hasCompactSupport.mul_right

omit [IsManifold I4 ∞ M] [T2Space M] in
private theorem scalarRadialChartCorrection_support (c : M) (y : FourSpace)
    (χ : ContDiffBump y) (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) :
    tsupport (scalarRadialChartCorrection y χ) ⊆ (chartAt FourSpace c).target := by
  change tsupport ((χ : FourSpace → ℝ) * (fun z => ‖z - y‖ ^ 2 - χ.rOut ^ 2)) ⊆ _
  exact tsupport_mul_subset_left.trans (by simpa only [χ.tsupport_eq] using hs)

def scalarRadialChartFunction (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) : SmoothScalar (M := M) :=
  ⟨fun x => χ.rOut ^ 2 + scalarChartLift c (scalarRadialChartCorrection y χ) x,
    by
    change ContMDiff I4 𝓘(ℝ, ℝ) ∞ _
    exact (contMDiff_const (c := χ.rOut ^ 2)).add (scalarChartLift_smooth c _
      (scalarRadialChartCorrection_smooth y χ) (scalarRadialChartCorrection_compact y χ)
      (scalarRadialChartCorrection_support c y χ hs))⟩

theorem scalarRadialChartFunction_on_source (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {x : M}
    (hx : x ∈ (chartAt FourSpace c).source) :
    (scalarRadialChartFunction c y χ hs).val x = χ.rOut ^ 2 +
      χ (chartAt FourSpace c x) * (‖chartAt FourSpace c x - y‖ ^ 2 - χ.rOut ^ 2) := by
  change χ.rOut ^ 2 + scalarChartLift c _ x = _
  rw [scalarChartLift_on_source c _ hx]
  rfl

theorem scalarRadialChartFunction_off_source (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {x : M}
    (hx : x ∉ (chartAt FourSpace c).source) :
    (scalarRadialChartFunction c y χ hs).val x = χ.rOut ^ 2 := by
  change χ.rOut ^ 2 + scalarChartLift c _ x = _
  simp only [scalarChartLift, ite_eq_right hx, add_zero]

private theorem scalarRadialBlend_lower {u v t w : ℝ} (hu : t ≤ u) (hv : t ≤ v)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : t ≤ v + w * (u - v) := by
  have ha := mul_nonneg hw (sub_nonneg.mpr hu)
  have hb := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hv)
  nlinarith

theorem scalarRadialChartFunction_nonneg (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) (x : M) :
    0 ≤ (scalarRadialChartFunction c y χ hs).val x := by
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · rw [scalarRadialChartFunction_on_source c y χ hs hx]
    exact scalarRadialBlend_lower (sq_nonneg _) (sq_nonneg _) χ.nonneg χ.le_one
  · rw [scalarRadialChartFunction_off_source c y χ hs hx]
    exact sq_nonneg _

theorem scalarRadialChartFunction_on_inner (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ closedBall y χ.rIn) :
    (scalarRadialChartFunction c y χ hs).val ((chartAt FourSpace c).symm z) = ‖z - y‖ ^ 2 := by
  have hzt : z ∈ (chartAt FourSpace c).target :=
    hs (closedBall_subset_closedBall χ.rIn_lt_rOut.le hz)
  rw [scalarRadialChartFunction_on_source c y χ hs ((chartAt FourSpace c).map_target hzt),
    (chartAt FourSpace c).right_inv hzt, χ.one_of_mem_closedBall hz]
  ring

theorem scalarRadialChartFunction_small (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {x : M}
    (hx : (scalarRadialChartFunction c y χ hs).val x < χ.rIn ^ 2) :
    x ∈ (chartAt FourSpace c).source ∧ chartAt FourSpace c x ∈ ball y χ.rIn ∧
      (scalarRadialChartFunction c y χ hs).val x = ‖chartAt FourSpace c x - y‖ ^ 2 := by
  have hr : χ.rIn ^ 2 < χ.rOut ^ 2 :=
    (sq_lt_sq₀ χ.rIn_pos.le χ.rOut_pos.le).mpr χ.rIn_lt_rOut
  have hsource : x ∈ (chartAt FourSpace c).source := by
    by_contra hn
    rw [scalarRadialChartFunction_off_source c y χ hs hn] at hx
    exact (not_lt_of_ge hr.le) hx
  have hdist : ‖chartAt FourSpace c x - y‖ < χ.rIn := by
    by_contra hn
    have hsq : χ.rIn ^ 2 ≤ ‖chartAt FourSpace c x - y‖ ^ 2 :=
      (sq_le_sq₀ χ.rIn_pos.le (norm_nonneg _)).mpr (le_of_not_gt hn)
    have hlower := scalarRadialBlend_lower hsq hr.le
      (χ.nonneg (x := chartAt FourSpace c x)) (χ.le_one (x := chartAt FourSpace c x))
    rw [scalarRadialChartFunction_on_source c y χ hs hsource] at hx
    exact (not_lt_of_ge hlower) hx
  have hball : chartAt FourSpace c x ∈ ball y χ.rIn := by
    simpa only [mem_ball, dist_eq_norm] using hdist
  refine ⟨hsource, hball, ?_⟩
  rw [scalarRadialChartFunction_on_source c y χ hs hsource,
    χ.one_of_mem_closedBall (ball_subset_closedBall hball)]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonnegative scalar supersolution cannot have a zero at the outer
contact of a positive radial ball. The radial function is a genuine smooth
scalar; the chart construction supplies the stated annular bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M] [Nonempty M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalar_no_zero_at_radial_contact (d : ParallelMetricData g μ)
    (u q : SmoothScalar (M := M)) {a r η B δ : ℝ}
    (har : a < r) (hη : 0 < η) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hu : ∀ x, 0 ≤ u.val x) (hq : ∀ x, 0 ≤ q.val x)
    (hinner : ∀ x, q.val x ≤ a → δ ≤ u.val x)
    (hgrad : ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      η ≤ ∑ i, scalarGradient g q.val e i ^ 2)
    (hlap : ∀ e : FrameBundle g, scalarLaplacian g q.val e ≤ B)
    (hsuper : ∀ e : FrameBundle g, scalarLaplacian g u.val e ≤ 2 * u.val e.base)
    (x₀ : M) (hqx : q.val x₀ = r) (hux : u.val x₀ = 0) : False := by
  obtain ⟨k, hk, hlarge⟩ := scalar_barrier_parameter hη hB (by norm_num : (0 : ℝ) ≤ 2)
  let c := Real.exp (-k * r)
  let b := smoothScalarExponentialBarrier q k c
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hble (x : M) : b.val x ≤ 1 := by
    change Real.exp (-k * q.val x) - c ≤ 1
    have he : Real.exp (-k * q.val x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (hq x))
    have hc : 0 ≤ c := (Real.exp_pos _).le
    linarith
  have hbstrict (e : FrameBundle g) (he : u.val e.base < ε * b.val e.base) :
      2 * b.val e.base < scalarLaplacian g b.val e := by
    have hbpos : 0 < b.val e.base :=
      (mul_pos_iff_of_pos_left hε).mp (lt_of_le_of_lt (hu e.base) he)
    have hqr : q.val e.base < r := by
      change 0 < Real.exp (-k * q.val e.base) - Real.exp (-k * r) at hbpos
      have ht := Real.exp_lt_exp.mp (sub_pos.mp hbpos)
      nlinarith
    have haq : a < q.val e.base := by
      by_contra hn
      have hi := hinner e.base (le_of_not_gt hn)
      have hbound := mul_le_mul_of_nonneg_left (hble e.base) hε.le
      dsimp only [ε] at he hbound
      linarith
    exact scalar_exponential_barrier_strict d q hk.le (Real.exp_pos _).le (by norm_num)
      e (hgrad e haq.le hqr.le) (hlap e) hlarge
  have hcompare : ∀ x, ε * b.val x ≤ u.val x :=
    scalar_barrier_comparison d u b hε (by norm_num) hsuper hbstrict
  have hbx : b.val x₀ = 0 := by
    change Real.exp (-k * q.val x₀) - Real.exp (-k * r) = 0
    rw [hqx, sub_self]
  let v := u - ε • b
  have hvx : v.val x₀ = 0 := by
    change u.val x₀ - ε * b.val x₀ = 0
    rw [hux, hbx, mul_zero, sub_zero]
  have humin : IsLocalMin u.val x₀ := Eventually.of_forall (fun x => by
    rw [hux]
    exact hu x)
  have hvmin : IsLocalMin v.val x₀ := Eventually.of_forall (fun x => by
    rw [hvx]
    exact sub_nonneg.mpr (hcompare x))
  let e := frameAt g x₀
  have hbgrad (i : Fin 4) : scalarGradient g b.val e i = 0 := by
    have hu0 := scalarGradient_zero_of_local_min d u e humin i
    have hv0 := scalarGradient_zero_of_local_min d v e hvmin i
    change (smoothScalarGradient d i (u - ε • b)) e = 0 at hv0
    rw [map_sub, map_smul] at hv0
    change scalarGradient g u.val e i - ε * scalarGradient g b.val e i = 0 at hv0
    have hm : ε * scalarGradient g b.val e i = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hε)
  have hqgrad (i : Fin 4) : scalarGradient g q.val e i = 0 := by
    have hi := hbgrad i
    change scalarGradient g (smoothScalarExponentialBarrier q k c).val e i = 0 at hi
    rw [smoothScalarExponentialBarrier_gradient d] at hi
    exact (mul_eq_zero.mp hi).resolve_left
      (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hk)) (ne_of_gt (Real.exp_pos _)))
  have hlast := hgrad e (by change a ≤ q.val x₀; rw [hqx]; exact har.le)
    (by change q.val x₀ ≤ r; rw [hqx])
  simp only [hqgrad, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hlast
  exact (not_le_of_gt hη) hlast

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact Lebesgue scaling and L² pullback for the affine coordinates used
to freeze the metric at a chart point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ENNReal

noncomputable section

def scalarAffineJacobian (A : FourSpace ≃L[ℝ] FourSpace) : ℝ :=
  |(LinearMap.det A.toLinearMap)⁻¹|

theorem scalarAffineJacobian_pos (A : FourSpace ≃L[ℝ] FourSpace) :
    0 < scalarAffineJacobian A := by
  exact abs_pos.mpr (inv_ne_zero (A.toLinearEquiv.isUnit_det'.ne_zero))

theorem scalarAffine_map_volume (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace) :
    Measure.map (fun x => A x + q) (volume : Measure FourSpace) =
      ENNReal.ofReal (scalarAffineJacobian A) • volume := by
  have hA : Measure.map A (volume : Measure FourSpace) =
      ENNReal.ofReal (scalarAffineJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map ((fun x : FourSpace => x + q) ∘ A) volume = _
  rw [← Measure.map_map (by fun_prop) A.continuous.measurable, hA,
    Measure.map_smul _ (by fun_prop), map_add_right_eq_self]

theorem scalarAffine_integral (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (f : FourSpace → ℝ) :
    (∫ x, f (A x + q)) = scalarAffineJacobian A * ∫ x, f x := by
  have he : MeasurableEmbedding (fun x => A x + q) :=
    (A.toHomeomorph.trans (Homeomorph.addRight q)).measurableEmbedding
  rw [← he.integral_map, scalarAffine_map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarAffineJacobian_pos A).le, smul_eq_mul]

theorem scalarAffine_memLp (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    {f : FourSpace → ℝ} (hf : MemLp f 2 (volume : Measure FourSpace)) :
    MemLp (fun x => f (A x + q)) 2 volume := by
  have hscaled := hf.smul_measure (c := ENNReal.ofReal (scalarAffineJacobian A))
    ENNReal.ofReal_ne_top
  rw [← scalarAffine_map_volume A q] at hscaled
  exact hscaled.comp_of_map (by fun_prop)

def scalarAffinePullbackL2 (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) : Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarAffine_memLp A q (Lp.memLp f)).toLp _

theorem scalarAffinePullbackL2_coe (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarAffinePullbackL2 A q f =ᵐ[volume] (fun x => f (A x + q)) :=
  MemLp.coeFn_toLp (scalarAffine_memLp A q (Lp.memLp f))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate Laplacian under an affine change of variables. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

def scalarPartialVector (ψ : FourSpace → ℝ) (z : FourSpace) : Fin 4 → ℝ :=
  fun i => partialDeriv ψ i z

def scalarPartialMatrix (ψ : FourSpace → ℝ) (z : FourSpace) : Mat4 :=
  fun i j => partialDeriv (fun w => partialDeriv ψ j w) i z

def scalarPrincipalContraction (H Q : Mat4) : ℝ := ∑ i, ∑ j, H i j * Q i j

theorem scalarPrincipalContraction_eq_trace (H Q : Mat4) :
    scalarPrincipalContraction H Q = (H * Qᵀ).trace := by
  simp only [scalarPrincipalContraction, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.transpose_apply]

theorem scalarAffineMap_partialVector (C : Mat4) (q z : FourSpace)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    scalarPartialVector (fun w => ψ (scalarAffineMap C q w)) z =
      Cᵀ *ᵥ scalarPartialVector ψ (scalarAffineMap C q z) := by
  funext i
  exact scalarAffineMap_partial C q z ψ (hψ.differentiable (by simp) _) i

theorem scalarAffineMap_partialMatrix (C : Mat4) (q z : FourSpace)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    scalarPartialMatrix (fun w => ψ (scalarAffineMap C q w)) z =
      Cᵀ * scalarPartialMatrix ψ (scalarAffineMap C q z) * C := by
  ext i j
  rw [scalarPartialMatrix, scalarAffineMap_partial_second C q z ψ hψ i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp [scalarPartialMatrix]
  ring

theorem scalarPrincipalContraction_affine (H C Q : Mat4) :
    scalarPrincipalContraction H (Cᵀ * Q * C) =
      scalarPrincipalContraction (C * H * Cᵀ) Q := by
  rw [scalarPrincipalContraction_eq_trace, scalarPrincipalContraction_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (H * (Cᵀ * (Qᵀ * C))).trace = (H * Cᵀ * Qᵀ * C).trace := by
      congr 1
      noncomm_ring
    _ = (C * (H * Cᵀ * Qᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (C * H * Cᵀ * Qᵀ).trace := by congr 1; noncomm_ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarChartDrift (g : SmoothMetric M) (c : M) (z : FourSpace) : Fin 4 → ℝ :=
  fun a => ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j * christoffel g c z a i j

theorem scalarChartOperator_eq_contraction (g : SmoothMetric M) (c : M)
    (ψ : FourSpace → ℝ) (z : FourSpace) :
    scalarChartOperator g c ψ z =
      scalarPrincipalContraction (metricInChart g c z)⁻¹ (scalarPartialMatrix ψ z) -
        scalarChartDrift g c z ⬝ᵥ scalarPartialVector ψ z := by
  have hs : (∑ a, (∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
      christoffel g c z a i j) * partialDeriv ψ a z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        (∑ a, christoffel g c z a i j * partialDeriv ψ a z) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  simp only [scalarChartOperator, scalarPrincipalContraction, scalarPartialMatrix,
    scalarChartDrift, scalarPartialVector, dotProduct, mul_sub, Finset.sum_sub_distrib]
  rw [hs]

theorem scalarChartOperator_affine (g : SmoothMetric M) (c : M)
    (C : Mat4) (q z : FourSpace) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    scalarChartOperator g c (fun w => ψ (scalarAffineMap C q w)) z =
      scalarPrincipalContraction (C * (metricInChart g c z)⁻¹ * Cᵀ)
        (scalarPartialMatrix ψ (scalarAffineMap C q z)) -
      (C *ᵥ scalarChartDrift g c z) ⬝ᵥ scalarPartialVector ψ (scalarAffineMap C q z) := by
  rw [scalarChartOperator_eq_contraction, scalarAffineMap_partialMatrix C q z ψ hψ,
    scalarPrincipalContraction_affine, scalarAffineMap_partialVector C q z ψ hψ,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Quantitative comparison between local coordinate L² and the actual
normalized Riemannian L² norm. The constant depends only on the compact chart
set and metric, not on the scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalarChart_eLpNorm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ f : M → ℝ,
      eLpNorm (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) 2
        (volume.restrict K) ≤ C * eLpNorm f 2 (normalizedVolume g) := by
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let S : Set (ChartTarget c) := Subtype.val ⁻¹' K
  let φ : ChartTarget c → M := fun z => (chartAt FourSpace c).symm z.val
  have hS : MeasurableSet S := measurable_subtype_coe hK.isClosed.measurableSet
  have hφ : MeasurableEmbedding φ :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  obtain ⟨δ, hδ, hδK⟩ := scalarChart_density_lower_bound g c hK hKt
  let d := ENNReal.ofReal δ
  have hd₀ : d ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hdtop : d ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  obtain ⟨hF₀, hFtop⟩ := ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)
  have hmeasure : d • μ.restrict S ≤ (μ.withDensity ρ).restrict S := by
    rw [← withDensity_const, restrict_withDensity hS]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with z hz
    exact ENNReal.ofReal_le_ofReal (hδK z.val hz)
  have hdom : μ.restrict S ≤ d⁻¹ • μ.withDensity ρ := by
    calc
      μ.restrict S = d⁻¹ • (d • μ.restrict S) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hd₀ hdtop, one_smul]
      _ ≤ d⁻¹ • (μ.withDensity ρ).restrict S := smul_le_smul_left _ hmeasure
      _ ≤ d⁻¹ • μ.withDensity ρ := by
        gcongr
        exact Measure.restrict_le_self
  have hbase : Measure.map φ (μ.withDensity ρ) =
      (normalizedChartFactor g)⁻¹ • (normalizedVolume g).restrict (chartAt FourSpace c).source := by
    rw [normalizedVolume_restrict_chart, smul_smul,
      ENNReal.inv_mul_cancel hF₀.ne' hFtop.ne, one_smul]
  let D := d⁻¹ * (normalizedChartFactor g)⁻¹
  have hDtop : D ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr hd₀) (ENNReal.inv_ne_top.mpr hF₀.ne')
  have hmapdom : Measure.map φ (μ.restrict S) ≤ D • normalizedVolume g := by
    calc
      Measure.map φ (μ.restrict S) ≤ Measure.map φ (d⁻¹ • μ.withDensity ρ) :=
        Measure.map_mono hdom hφ.measurable
      _ = D • (normalizedVolume g).restrict (chartAt FourSpace c).source := by
        rw [Measure.map_smul _ hφ.measurable.aemeasurable, hbase, smul_smul]
      _ ≤ D • normalizedVolume g := by
        gcongr
        exact Measure.restrict_le_self
  have he := MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet
  have hmap : Measure.map (Subtype.val : ChartTarget c → FourSpace) (μ.restrict S) =
      volume.restrict K := by
    rw [← he.restrict_map]
    change (Measure.map Subtype.val (Measure.comap Subtype.val volume)).restrict K = _
    rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet,
      inter_eq_left.mpr hKt]
  refine ⟨D ^ (1 / (2 : ℝ≥0∞)).toReal, ?_, ?_⟩
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hDtop
  · intro f
    rw [← hmap, he.eLpNorm_map_measure]
    change eLpNorm (f ∘ φ) 2 (μ.restrict S) ≤ _
    rw [← hφ.eLpNorm_map_measure]
    exact eLpNorm_le_of_measure_le_smul hmapdom

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous weak supersolution is positive inside a radial barrier.
The comparison barrier stays positive at the alleged zero, so no
pointwise derivative of the weak solution is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance continuousRadial_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_no_zero_inside_radial_barrier (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (q : SmoothScalar (M := M)) {a r η B δ : ℝ}
    (hη : 0 < η) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hu : ∀ x, 0 ≤ f x) (hq : ∀ x, 0 ≤ q.val x)
    (hinner : ∀ x, q.val x ≤ a → δ ≤ f x)
    (hgrad : ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      η ≤ ∑ i, scalarGradient g q.val e i ^ 2)
    (hlap : ∀ e : FrameBundle g, scalarLaplacian g q.val e ≤ B)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (x₀ : M) (hqx : q.val x₀ < r) (hux : f x₀ = 0) : False := by
  obtain ⟨k, hk, hlarge⟩ := scalar_barrier_parameter hη hB (by norm_num : (0 : ℝ) ≤ 2)
  let c := Real.exp (-k * r)
  let b := smoothScalarExponentialBarrier q k c
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hble (x : M) : b.val x ≤ 1 := by
    change Real.exp (-k * q.val x) - c ≤ 1
    have he : Real.exp (-k * q.val x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (hq x))
    have hc : 0 ≤ c := (Real.exp_pos _).le
    linarith
  have hbstrict (e : FrameBundle g) (he : f e.base < ε * b.val e.base) :
      2 * b.val e.base < scalarLaplacian g b.val e := by
    have hbpos : 0 < b.val e.base :=
      (mul_pos_iff_of_pos_left hε).mp (lt_of_le_of_lt (hu e.base) he)
    have hqr : q.val e.base < r := by
      change 0 < Real.exp (-k * q.val e.base) - Real.exp (-k * r) at hbpos
      have ht := Real.exp_lt_exp.mp (sub_pos.mp hbpos)
      nlinarith
    have haq : a < q.val e.base := by
      by_contra hn
      have hi := hinner e.base (le_of_not_gt hn)
      have hbound := mul_le_mul_of_nonneg_left (hble e.base) hε.le
      dsimp only [ε] at he hbound
      linarith
    exact scalar_exponential_barrier_strict d q hk.le (Real.exp_pos _).le (by norm_num)
      e (hgrad e haq.le hqr.le) (hlap e) hlarge
  have hcompare : ∀ x, ε * b.val x ≤ f x :=
    scalarH1_barrier_comparison g o d u F heq f hf hrep b hε (by norm_num) hsource hbstrict
  have hbx : 0 < b.val x₀ := by
    change 0 < Real.exp (-k * q.val x₀) - Real.exp (-k * r)
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hc := hcompare x₀
  rw [hux] at hc
  exact (not_le_of_gt (mul_pos hε hbx)) hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! A coordinate bound for every orthonormal-frame gradient component.
This is the reverse estimate needed to transport local derivative integrability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_frame_gradient_sq_le_chart (g : SmoothMetric M) (a : SmoothScalar (M := M))
    (c : M) (z : ChartTarget c) (e : FrameBundle g)
    (he : e.base = (chartAt FourSpace c).symm z) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C) (i : Fin 4) :
    scalarGradient g a.val e i ^ 2 ≤ 16 * C ^ 2 *
      ∑ j, (partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z) ^ 2 := by
  let p := fun j => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z
  have hrow (k : Fin 4) : (∑ j, chartGramMatrix g c 1 z j k * p j) ^ 2 ≤
      (4 * C ^ 2) * ∑ j, p j ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => chartGramMatrix g c 1 z j k) p
    have hsum : (∑ j : Fin 4, chartGramMatrix g c 1 z j k ^ 2) ≤ 4 * C ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin 4, C ^ 2 := Finset.sum_le_sum fun j _ => by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hE j k)
        _ = _ := by simp
    exact hcs.trans (mul_le_mul_of_nonneg_right hsum
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    scalarGradient g a.val e i ^ 2 ≤ ∑ k, scalarGradient g a.val e k ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (scalarGradient g a.val e k)) (Finset.mem_univ i)
    _ = scalarDirichletDensity g a.val e.base := (scalarDirichletDensity_eq_frame g a.val e).symm
    _ = ∑ k, (∑ j, chartGramMatrix g c 1 z j k * p j) ^ 2 := by
      rw [he]
      have hden := scalarDirichletDensity_eq_frame g a.val (chartGramSection g c 1 (by simp) z)
      change scalarDirichletDensity g a.val ((chartAt FourSpace c).symm z) = _ at hden
      rw [hden]
      simp_rw [scalarGradient_chart g a.property c z]
      rfl
    _ ≤ ∑ _k : Fin 4, (4 * C ^ 2) * ∑ j, p j ^ 2 :=
      Finset.sum_le_sum (fun k _ => hrow k)
    _ = _ := by simp; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate equation with an actual L2 source for the H1 solution supplied by the
variational solver. This keeps its weak coordinate derivatives and its
distributional Poisson equation attached to one representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance h1EquationL2_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance h1EquationL2_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem scalarH1_L2_weak_base_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v))) (v : SmoothScalar (M := M)) :
    inner ℝ (scalarH1BaseValue g o d u) (smoothScalarBaseL2 g (smoothScalarLaplacian g v)) =
      inner ℝ f (smoothScalarBaseL2 g v) := by
  have h := hw (smoothScalarToH1 d v)
  change (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u)
    (smoothScalarGradientL2 d i v)) =
      -(inner ℝ (scalarBasePullback g o f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v)) at h
  have hg := scalarH1_green d u v
  have he : inner ℝ (scalarH1Value d u)
      (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) =
      inner ℝ (scalarBasePullback g o f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v) := by linarith
  calc
    _ = inner ℝ (scalarBasePullback g o (scalarH1BaseValue g o d u))
        (scalarBasePullback g o (smoothScalarBaseL2 g (smoothScalarLaplacian g v))) :=
      ((scalarBasePullback g o).inner_map_map _ _).symm
    _ = inner ℝ (scalarH1Value d u)
        (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) := by
      rw [scalarH1BaseValue_spec, scalarBasePullback_smooth, smoothScalarLaplacian_valueL2]
    _ = _ := by
      rw [he, ← scalarBasePullback_smooth g o v,
        (scalarBasePullback g o).inner_map_map]

theorem scalarH1_L2_weak_coordinate_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v)))
    (c : M) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    (∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
      (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
        scalarChartOperator g c ψ z)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (f ((chartAt FourSpace c).symm z) * ψ z) := by
  let b := scalarH1BaseValue g o d u
  have h := scalarH1_L2_weak_base_distribution g o d f u hw (scalarChartTest c ψ hψ hc hs)
  rw [smoothScalarBaseL2_inner_right, smoothScalarBaseL2_inner_right] at h
  have hsupport := scalarChartLift_tsupport c ψ hc hs
  have hleft : ∀ x, x ∉ (chartAt FourSpace c).source →
      b x * scalarLaplacianBase g (scalarChartLift c ψ) x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsupport (scalarLaplacianBase_tsupport g _ ht))), mul_zero]
  have hright : ∀ x, x ∉ (chartAt FourSpace c).source →
      f x * scalarChartLift c ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupport ht)), mul_zero]
  change (∫ x, b x * scalarLaplacianBase g (scalarChartLift c ψ) x ∂normalizedVolume g) =
    ∫ x, f x * scalarChartLift c ψ x ∂normalizedVolume g at h
  rw [normalizedVolume_integral_chart g c _ hleft,
    normalizedVolume_integral_chart g c _ hright] at h
  apply (mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne') at h
  calc
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (b ((chartAt FourSpace c).symm z) *
          scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z)) := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartTest_laplacian g c ψ hψ hc hs z hz]
    _ = _ := h
    _ = _ := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartLift_symm c ψ hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial chart function has a nonvanishing actual metric
differential on every punctured inner ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

theorem scalarRadialChartFunction_eventually (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ ball y χ.rIn) :
    (fun w => (scalarRadialChartFunction c y χ hs).val ((chartAt FourSpace c).symm w))
      =ᶠ[𝓝 z] fun w => ‖w - y‖ ^ 2 := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact scalarRadialChartFunction_on_inner c y χ hs (ball_subset_closedBall hw)

theorem scalarRadialChartFunction_partial (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ ball y χ.rIn) (i : Fin 4) :
    partialDeriv
      (fun w => (scalarRadialChartFunction c y χ hs).val ((chartAt FourSpace c).symm w)) i z =
        2 * (z i - y i) := by
  unfold partialDeriv
  rw [(scalarRadialChartFunction_eventually c y χ hs hz).fderiv_eq]
  have hd := ((hasFDerivAt_id z).sub_const y).norm_sq
  have hd' : fderiv ℝ (fun w : FourSpace => ‖w - y‖ ^ 2) z =
      2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ FourSpace) := by
    simpa only [id_eq] using hd.fderiv
  rw [hd']
  have hb : coordinateVector i = (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_apply, innerSL_apply_apply, nsmul_eq_mul, hb,
    EuclideanSpace.inner_basisFun_real]
  rfl

theorem scalarRadialChartFunction_density_pos (g : SmoothMetric M) (c : M)
    (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ ball y χ.rIn) (hzy : z ≠ y) :
    0 < scalarDirichletDensity g (scalarRadialChartFunction c y χ hs).val
      ((chartAt FourSpace c).symm z) := by
  let a := scalarRadialChartFunction c y χ hs
  have hzt : z ∈ (chartAt FourSpace c).target :=
    hs (closedBall_subset_closedBall χ.rIn_lt_rOut.le (ball_subset_closedBall hz))
  by_contra hn
  have hzero : scalarDirichletDensity g a.val ((chartAt FourSpace c).symm z) = 0 :=
    le_antisymm (le_of_not_gt hn) (scalarDirichletDensity_nonneg g a.val _)
  apply hzy
  ext i
  have h := scalarCoordinate_gradient_sq_le g a.property c ⟨z, hzt⟩ i
  rw [hzero, mul_zero] at h
  have hp := scalarRadialChartFunction_partial c y χ hs hz i
  change partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z = _ at hp
  rw [hp] at h
  nlinarith [sq_nonneg (2 * (z i - y i))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial contact contradiction needs only first derivatives of the
weak solution along actual frame curves. Second derivatives are needed
only for the explicitly smooth barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalar_barrier_gradient_zero_at_first_order_contact
    (d : ParallelMetricData g μ) (f : M → ℝ)
    (hfd : ∀ (i : Fin 4) (e : FrameBundle g), DifferentiableAt ℝ
      (fun t : ℝ => f (((d.toMetricGreenData.flow i).map t) e).base) 0)
    (b : SmoothScalar (M := M)) {ε : ℝ} (hε : 0 < ε)
    (hfn : ∀ x, 0 ≤ f x) (hcompare : ∀ x, ε * b.val x ≤ f x)
    (x₀ : M) (hfx : f x₀ = 0) (hbx : b.val x₀ = 0)
    (i : Fin 4) : scalarGradient g b.val (frameAt g x₀) i = 0 := by
  let e := frameAt g x₀
  let φ := d.toMetricGreenData.flow i
  obtain ⟨z, hz⟩ := (φ.map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 z = e at hz
  have hf0 : f (φ.map 0 z).base = 0 := by
    change f (((d.toMetricGreenData.flow i).map 0) z).base = 0
    rw [hz]
    exact hfx
  have hb0 : b.val (φ.map 0 z).base = 0 := by
    change b.val (((d.toMetricGreenData.flow i).map 0) z).base = 0
    rw [hz]
    exact hbx
  have hdf := (hfd i z).hasDerivAt
  have hmin : IsLocalMin (fun t : ℝ => f (φ.map t z).base) 0 := by
    apply Eventually.of_forall
    intro t
    change f (φ.map 0 z).base ≤ f (φ.map t z).base
    rw [hf0]
    exact hfn _
  have hdz := hmin.hasDerivAt_eq_zero hdf
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  have hdb := sb.derivativeValue i 0 z
  have hmin' : IsLocalMin (fun t : ℝ => f (φ.map t z).base - ε * b.val (φ.map t z).base) 0 := by
    apply Eventually.of_forall
    intro t
    change f (φ.map 0 z).base - ε * b.val (φ.map 0 z).base ≤
      f (φ.map t z).base - ε * b.val (φ.map t z).base
    rw [hf0, hb0, mul_zero, sub_zero]
    exact sub_nonneg.mpr (hcompare _)
  have hvz := hmin'.hasDerivAt_eq_zero (hdf.sub (hdb.const_mul ε))
  rw [hdz, zero_sub, neg_eq_zero] at hvz
  have hz' := (mul_eq_zero.mp hvz).resolve_left hε.ne'
  simpa only [hz] using hz'

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance weakContact_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_no_zero_at_radial_contact (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hfd : ∀ (i : Fin 4) (e : FrameBundle g), DifferentiableAt ℝ
      (fun t : ℝ => f (((d.toMetricGreenData.flow i).map t) e).base) 0)
    (q : SmoothScalar (M := M)) {a r η B δ : ℝ}
    (har : a < r) (hη : 0 < η) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hu : ∀ x, 0 ≤ f x) (hq : ∀ x, 0 ≤ q.val x)
    (hinner : ∀ x, q.val x ≤ a → δ ≤ f x)
    (hgrad : ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      η ≤ ∑ i, scalarGradient g q.val e i ^ 2)
    (hlap : ∀ e : FrameBundle g, scalarLaplacian g q.val e ≤ B)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (x₀ : M) (hqx : q.val x₀ = r) (hux : f x₀ = 0) : False := by
  obtain ⟨k, hk, hlarge⟩ := scalar_barrier_parameter hη hB (by norm_num : (0 : ℝ) ≤ 2)
  let c := Real.exp (-k * r)
  let b := smoothScalarExponentialBarrier q k c
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hble (x : M) : b.val x ≤ 1 := by
    change Real.exp (-k * q.val x) - c ≤ 1
    have he : Real.exp (-k * q.val x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (hq x))
    have hc : 0 ≤ c := (Real.exp_pos _).le
    linarith
  have hbstrict (e : FrameBundle g) (he : f e.base < ε * b.val e.base) :
      2 * b.val e.base < scalarLaplacian g b.val e := by
    have hbpos : 0 < b.val e.base :=
      (mul_pos_iff_of_pos_left hε).mp (lt_of_le_of_lt (hu e.base) he)
    have hqr : q.val e.base < r := by
      change 0 < Real.exp (-k * q.val e.base) - Real.exp (-k * r) at hbpos
      have ht := Real.exp_lt_exp.mp (sub_pos.mp hbpos)
      nlinarith
    have haq : a < q.val e.base := by
      by_contra hn
      have hi := hinner e.base (le_of_not_gt hn)
      have hbound := mul_le_mul_of_nonneg_left (hble e.base) hε.le
      dsimp only [ε] at he hbound
      linarith
    exact scalar_exponential_barrier_strict d q hk.le (Real.exp_pos _).le (by norm_num)
      e (hgrad e haq.le hqr.le) (hlap e) hlarge
  have hcompare : ∀ x, ε * b.val x ≤ f x :=
    scalarH1_barrier_comparison g o d u F heq f hf hrep b hε (by norm_num) hsource hbstrict
  have hbx : b.val x₀ = 0 := by
    change Real.exp (-k * q.val x₀) - Real.exp (-k * r) = 0
    rw [hqx, sub_self]
  let e := frameAt g x₀
  have hbgrad (i : Fin 4) : scalarGradient g b.val e i = 0 :=
    scalar_barrier_gradient_zero_at_first_order_contact d f hfd b hε hu hcompare x₀ hux hbx i
  have hqgrad (i : Fin 4) : scalarGradient g q.val e i = 0 := by
    have hi := hbgrad i
    change scalarGradient g (smoothScalarExponentialBarrier q k c).val e i = 0 at hi
    rw [smoothScalarExponentialBarrier_gradient d] at hi
    exact (mul_eq_zero.mp hi).resolve_left
      (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hk)) (ne_of_gt (Real.exp_pos _)))
  have hlast := hgrad e (by change a ≤ q.val x₀; rw [hqx]; exact har.le)
    (by change q.val x₀ ≤ r; rw [hqx])
  simp only [hqgrad, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hlast
  exact (not_le_of_gt hη) hlast

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic energy controls the local coordinate L² differential.
These estimates are uniform over the smooth scalars generating H¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartEnergy_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance chartEnergy_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def scalarEnergyRoot (g : SmoothMetric M) (a : SmoothScalar (M := M)) : C(M, ℝ) :=
  ⟨fun x => Real.sqrt (scalarDirichletDensity g a x),
    Real.continuous_sqrt.comp (scalarDirichletDensity_continuous g a.property)⟩

def scalarEnergyRootL2 (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarEnergyRoot g a)

theorem scalarEnergyRootL2_norm_sq (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    ‖scalarEnergyRootL2 g a‖ ^ 2 = smoothScalarDirichlet d a a := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarEnergyRoot g a))
    (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarEnergyRoot g a)) = _
  rw [ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  have hs : (∫ x, (scalarEnergyRoot g a) x * (scalarEnergyRoot g a) x
      ∂normalizedVolume g) = ∫ x, scalarDirichletDensity g a x ∂normalizedVolume g := by
    apply integral_congr_ae
    filter_upwards with x
    change Real.sqrt (scalarDirichletDensity g a x) *
      Real.sqrt (scalarDirichletDensity g a x) = _
    rw [← pow_two, Real.sq_sqrt (scalarDirichletDensity_nonneg g a x)]
  rw [hs, smoothScalarDirichlet_eq_integral]
  rw [← (canonicalFrameMeasure_base g o).map_eq,
    integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable
      (by simpa only [(canonicalFrameMeasure_base g o).map_eq] using
        (scalarDirichletDensity_continuous g a.property).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with e
  rw [scalarDirichletDensity_eq_frame]
  simp only [pow_two]

theorem scalarEnergyRootL2_norm_le (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    ‖scalarEnergyRootL2 g a‖ ≤ ‖smoothScalarToH1 d a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [scalarEnergyRootL2_norm_sq g o d, scalarH1_norm_sq]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth, smoothScalarDirichlet,
    real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarCoordinate_gradient_abs_le (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (i : Fin 4) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ (a : M → ℝ), ContMDiff I4 𝓘(ℝ, ℝ) ∞ a →
      ∀ z ∈ K, (partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z) ^ 2 ≤
        A * scalarDirichletDensity g a ((chartAt FourSpace c).symm z))
    (a : SmoothScalar (M := M)) {z : FourSpace} (hz : z ∈ K) :
    |partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z| ≤
      Real.sqrt A * (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z) := by
  have h := hbound a a.property z hz
  have hsA := Real.sq_sqrt hA
  have hsD := Real.sq_sqrt (scalarDirichletDensity_nonneg g a ((chartAt FourSpace c).symm z))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hsA, hsD]
  exact h

theorem scalarChart_norm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ) (hf : MemLp f 2 (normalizedVolume g))
      (hchart : MemLp (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) 2
        (volume.restrict K)),
      ‖hchart.toLp _‖ ≤ C * ‖hf.toLp f‖ := by
  obtain ⟨C, hC, hbound⟩ := scalarChart_eLpNorm_bound g c hK hKt
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f hf hchart
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hf.eLpNorm_ne_top) (hbound f)
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul] using h

theorem scalarCoordinate_gradient_memLp (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (a : SmoothScalar (M := M)) (i : Fin 4) :
    MemLp (fun z : FourSpace =>
      partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) 2
      (volume.restrict K) := by
  have hcont : ContinuousOn (fun z : FourSpace =>
      partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) K := by
    intro z hz
    have hs : ContDiffAt ℝ ∞ (fun w => a.val ((chartAt FourSpace c).symm w)) z :=
      scalarCoordinates_contDiffAt a.property c z (hKt hz) (fun j => Fin.elim0 j)
    exact ((hs.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).continuousAt.continuousWithinAt
  obtain ⟨A, hA, hbound⟩ := scalarCoordinate_gradient_sq_le_on_compact g c hK hKt i
  have hroot := scalarChartL2_compact g c (scalarEnergyRootL2 g a) hK hKt
  have hroot' : MemLp (fun z : FourSpace =>
      (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) := by
    have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (scalarEnergyRoot g a)
    -- The chart comparison transfers the base almost-everywhere equality.
    have hzero := scalarChart_eLpNorm_bound g c hK hKt
    obtain ⟨B, _hB, hBbound⟩ := hzero
    have hdiff : eLpNorm (fun z : FourSpace =>
        scalarEnergyRootL2 g a ((chartAt FourSpace c).symm z) -
          (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) = 0 := by
      apply le_antisymm
      swap
      · exact zero_le
      have hh := hBbound (fun x => scalarEnergyRootL2 g a x - (scalarEnergyRoot g a) x)
      have hz : (fun x => scalarEnergyRootL2 g a x - (scalarEnergyRoot g a) x) =ᵐ[normalizedVolume g] 0 :=
        he.mono (fun _ hx => sub_eq_zero.mpr hx)
      simpa only [eLpNorm_congr_ae hz, eLpNorm_zero, mul_zero] using hh
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hdiff
    apply hroot.ae_eq
    filter_upwards [hae] with z hz
    exact sub_eq_zero.mp hz
  apply hroot'.of_le_mul (c := Real.sqrt A)
    (hcont.aestronglyMeasurable hK.isClosed.measurableSet)
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  change |partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z| ≤
    Real.sqrt A * |Real.sqrt (scalarDirichletDensity g a ((chartAt FourSpace c).symm z))|
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact scalarCoordinate_gradient_abs_le g c i A hA hbound a hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reverse chart norm control on a compact coordinate set. This is the
measure comparison needed to assemble local Sobolev estimates on the base. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalarChart_reverse_eLpNorm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ D : ℝ≥0∞, D ≠ (∞ : ℝ≥0∞) ∧ ∀ (p : ℝ≥0∞) (f : M → ℝ),
      support f ⊆ (chartAt FourSpace c).symm '' K →
      eLpNorm f p (normalizedVolume g) ≤ D ^ (1 / p).toReal *
        eLpNorm (fun z => f ((chartAt FourSpace c).symm z)) p (volume.restrict K) := by
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let T : Set (ChartTarget c) := Subtype.val ⁻¹' K
  let φ : ChartTarget c → M := fun z => (chartAt FourSpace c).symm z.val
  have hT : MeasurableSet T := measurable_subtype_coe hK.isClosed.measurableSet
  have hφ : MeasurableEmbedding φ :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  have hS : MeasurableSet (φ '' T) := hφ.measurableSet_image' hT
  have hsource : φ '' T ⊆ (chartAt FourSpace c).source := by
    rintro _ ⟨z, _, rfl⟩
    exact (chartAt FourSpace c).map_target z.property
  have himage : φ '' T = (chartAt FourSpace c).symm '' K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hKt hz⟩, hz, rfl⟩
  have hρcont : ContinuousOn (fun z => chartVolumeDensity g c z) K :=
    fun z hz => (chartVolumeDensity_contDiffAt g c z (hKt hz)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hρcont).isBounded.exists_norm_le
  let b := ENNReal.ofReal (max B 0)
  have hdom : (μ.withDensity ρ).restrict T ≤ b • μ.restrict T := by
    rw [← withDensity_const, restrict_withDensity hT]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hT] with z hz
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans ((hB _ ⟨z.val, hz, rfl⟩).trans (le_max_left _ _))
  have hbase : (normalizedVolume g).restrict (φ '' T) =
      normalizedChartFactor g • Measure.map φ ((μ.withDensity ρ).restrict T) := by
    calc
      _ = ((normalizedVolume g).restrict (chartAt FourSpace c).source).restrict (φ '' T) := by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr hsource]
      _ = _ := by
        rw [normalizedVolume_restrict_chart, Measure.restrict_smul, hφ.restrict_map,
          hφ.injective.preimage_image]
  let D := normalizedChartFactor g * b
  have hD : D ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top
    (ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)).2.ne ENNReal.ofReal_ne_top
  have hmeasure : (normalizedVolume g).restrict (φ '' T) ≤
      D • Measure.map φ (μ.restrict T) := by
    rw [hbase]
    calc
      _ ≤ normalizedChartFactor g • Measure.map φ (b • μ.restrict T) :=
        smul_le_smul_left _ (Measure.map_mono hdom hφ.measurable)
      _ = _ := by rw [Measure.map_smul _ hφ.measurable.aemeasurable, smul_smul]
  have he := MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet
  have hmap : Measure.map (Subtype.val : ChartTarget c → FourSpace) (μ.restrict T) =
      volume.restrict K := by
    rw [← he.restrict_map]
    change (Measure.map Subtype.val (Measure.comap Subtype.val volume)).restrict K = _
    rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_eq_left.mpr hKt]
  refine ⟨D, hD, fun p f hf => ?_⟩
  have hind : (φ '' T).indicator f = f := indicator_eq_self.mpr (himage.symm ▸ hf)
  have hn := eLpNorm_le_of_measure_le_smul (f := f) (p := p) hmeasure
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hS, hind,
    hφ.eLpNorm_map_measure] at hn
  have hright : eLpNorm (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) p
      (volume.restrict K) = eLpNorm (f ∘ φ) p (μ.restrict T) := by
    rw [← hmap, he.eLpNorm_map_measure]
    rfl
  rwa [hright]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A positive Euclidean ball tangent to the zero set near a boundary
point. The radius is obtained from a compact nearest-point argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped _root_.Topology

noncomputable section

theorem scalar_euclidean_positive_contact_ball
    (f : FourSpace → ℝ) (x y : FourSpace) {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall x (R / 2)))
    (hn : ∀ z ∈ closedBall x (R / 2), 0 ≤ f z)
    (hx : f x = 0) (hy : dist y x < R / 4) (hfy : 0 < f y) :
    ∃ (r : ℝ) (z : FourSpace), 0 < r ∧ r ≤ dist y x ∧ dist z y = r ∧ f z = 0 ∧
      closedBall y r ⊆ ball x (R / 2) ∧ ∀ w ∈ ball y r, 0 < f w := by
  let Z := closedBall x (R / 2) ∩ f ⁻¹' Iic 0
  have hZ : IsCompact Z :=
    hf.lowerSemicontinuousOn.isCompact_inter_preimage_Iic (isCompact_closedBall _ _) 0
  have hxZ : x ∈ Z := by
    exact ⟨mem_closedBall_self (by positivity), by
      simpa only [mem_preimage, mem_Iic, hx] using (le_refl (0 : ℝ))⟩
  obtain ⟨z, hz, hmin⟩ := hZ.exists_isMinOn ⟨x, hxZ⟩
    (show Continuous (fun z : FourSpace => dist z y) from
      continuous_id.dist continuous_const).continuousOn
  let r := dist z y
  have hr : 0 < r := by
    apply dist_pos.mpr
    intro he
    have hh : f y ≤ 0 := by simpa only [he, mem_preimage, mem_Iic] using hz.2
    exact (not_le_of_gt hfy) hh
  have hrx : r ≤ dist y x := by
    exact (hmin hxZ).trans_eq (dist_comm x y)
  have hsub : closedBall y r ⊆ ball x (R / 2) := by
    intro w hw
    have hw' : dist w y ≤ r := mem_closedBall.mp hw
    have ht := dist_triangle w y x
    apply mem_ball.mpr
    linarith
  refine ⟨r, z, hr, hrx, rfl, le_antisymm hz.2 (hn z hz.1), hsub, ?_⟩
  intro w hw
  have hwK : w ∈ closedBall x (R / 2) := ball_subset_closedBall (hsub (ball_subset_closedBall hw))
  by_contra hbad
  have hwZ : w ∈ Z := ⟨hwK, le_of_not_gt hbad⟩
  have hle : r ≤ dist w y := hmin hwZ
  exact (not_lt_of_ge hle) (mem_ball.mp hw)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute coordinate estimates for an arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_frame_gradient_abs_le_chart (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) (c : M) (z : ChartTarget c) (e : FrameBundle g)
    (he : e.base = (chartAt FourSpace c).symm z) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C) (i : Fin 4) :
    |scalarGradient g a.val e i| ≤ 4 * C *
      ∑ j, |partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z| := by
  let p := fun j => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z
  have hp : 0 ≤ ∑ j, |p j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hC) hp)).mp
  rw [sq_abs]
  have hs : ∑ j, p j ^ 2 ≤ (∑ j, |p j|) ^ 2 := by
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (p j)))
  calc
    _ ≤ 16 * C ^ 2 * ∑ j, p j ^ 2 := scalar_frame_gradient_sq_le_chart g a c z e he C hC hE i
    _ ≤ 16 * C ^ 2 * (∑ j, |p j|) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem scalar_chart_gram_bounded (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C := by
  have hb (j k : Fin 4) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ K, |chartGramMatrix g c 1 z j k| ≤ B := by
    have hc : ContinuousOn (fun z => chartGramMatrix g c 1 z j k) K :=
      fun z hz => (chartGramMatrix_contDiffAt g c 1 z (hKt hz) j k).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
    exact ⟨max B 0, le_max_right _ _, fun z hz =>
      (hB _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩
  choose B hB0 hB using hb
  refine ⟨∑ j, ∑ k, B j k,
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hB0 j k)), ?_⟩
  intro z hz j k
  exact (hB j k z hz).trans
    ((Finset.single_le_sum (fun k _ => hB0 j k) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ => hB0 j k))
        (Finset.mem_univ j)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact annular bounds for the actual smooth radial chart function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

local instance radialAnnulus_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

omit [CompactSpace M] in
theorem scalar_radial_annulus_gradient_pos (g : SmoothMetric M)
    (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {a r : ℝ}
    (ha : 0 < a) (hr : r < χ.rIn ^ 2) (e : FrameBundle g)
    (he₁ : a ≤ (scalarRadialChartFunction c y χ hs).val e.base)
    (he₂ : (scalarRadialChartFunction c y χ hs).val e.base ≤ r) :
    0 < ∑ i, scalarGradient g (scalarRadialChartFunction c y χ hs).val e i ^ 2 := by
  obtain ⟨hsource, hball, heq⟩ := scalarRadialChartFunction_small c y χ hs (he₂.trans_lt hr)
  have hneq : chartAt FourSpace c e.base ≠ y := by
    intro hy
    rw [hy, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at heq
    linarith
  have hp := scalarRadialChartFunction_density_pos g c y χ hs hball hneq
  rw [(chartAt FourSpace c).left_inv hsource] at hp
  rwa [scalarDirichletDensity_eq_frame g _ e] at hp

omit [T3Space M] in
theorem scalar_positive_annular_gradient_bound (g : SmoothMetric M)
    (q : SmoothScalar (M := M)) {a r : ℝ}
    (hne : ∃ e : FrameBundle g, a ≤ q.val e.base ∧ q.val e.base ≤ r)
    (hpos : ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      0 < ∑ i, scalarGradient g q.val e i ^ 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      η ≤ ∑ i, scalarGradient g q.val e i ^ 2 := by
  let K : Set (FrameBundle g) := {e | a ≤ q.val e.base ∧ q.val e.base ≤ r}
  have hq : Continuous (fun e : FrameBundle g => q.val e.base) :=
    q.property.continuous.comp (continuous_frameBase g)
  have hK : IsCompact K :=
    ((isClosed_le continuous_const hq).inter (isClosed_le hq continuous_const)).isCompact
  have hE : Continuous (fun e : FrameBundle g => ∑ i, scalarGradient g q.val e i ^ 2) :=
    continuous_finsetSum _ (fun i _ => (actual_scalarGradient_continuous g q.property i).pow 2)
  obtain ⟨e, he, hmin⟩ := hK.exists_isMinOn hne hE.continuousOn
  exact ⟨_, hpos e he.1 he.2, fun z hz₁ hz₂ => hmin ⟨hz₁, hz₂⟩⟩

omit [T3Space M] in
theorem scalar_laplacian_uniform_upper (g : SmoothMetric M) (q : SmoothScalar (M := M)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ e : FrameBundle g, scalarLaplacian g q.val e ≤ B := by
  have hL : Continuous (fun e : FrameBundle g => scalarLaplacian g q.val e) :=
    continuous_finsetSum _ (fun i _ => actual_scalarHessian_continuous g q.property i i)
  obtain ⟨B, hB⟩ := (isCompact_univ.image hL).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun e => ?_⟩
  exact (le_abs_self _).trans ((hB _ ⟨e, mem_univ _, rfl⟩).trans (le_max_left _ _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual invertible affine map used to rescale a metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frozenFrameLinearEquiv_symm_matrix (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) :
    (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap =
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)⁻¹ := by
  apply ContinuousLinearMap.ext
  intro v
  apply (frozenFrameLinearEquiv g c z₀).injective
  change (frozenFrameLinearEquiv g c z₀) ((frozenFrameLinearEquiv g c z₀).symm v) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change v = (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)
    ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)⁻¹ v)
  rw [← mul_apply_eq_comp, ← map_mul, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (chartGramMatrix_isUnit g c z₀)), map_one]
  rfl

def scalarRescalingLinearEquiv (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (hr : r ≠ 0) : FourSpace ≃L[ℝ] FourSpace :=
  ContinuousLinearEquiv.equivOfInverse
    (r • (frozenFrameLinearEquiv g c z₀).toContinuousLinearMap)
    (r⁻¹ • (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap)
    (by intro x; simp [smul_smul, hr])
    (by intro x; simp [smul_smul, hr])

theorem scalarRescalingLinearEquiv_apply (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (y : FourSpace) :
    scalarRescalingLinearEquiv g c z₀ r hr y + z₀ = scalarRescaledPoint g c z₀ r y := by
  change r • (frozenFrameLinearEquiv g c z₀ y) + z₀ = _
  rw [scalarRescaledPoint, add_comm]
  rfl

theorem scalarRescalingLinearEquiv_symm_apply (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (z : FourSpace) :
    (scalarRescalingLinearEquiv g c z₀ r hr).symm z =
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
        (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) z := by
  change r⁻¹ • (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap z = _
  rw [frozenFrameLinearEquiv_symm_matrix, map_smul]
  rfl

theorem scalarRescaling_inverse_affine (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (z : FourSpace) :
    (scalarRescalingLinearEquiv g c z₀ r hr).symm (z - z₀) =
      scalarAffineMap (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹)
        (-((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
          (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) z₀)) z := by
  rw [scalarRescalingLinearEquiv_symm_apply, map_sub]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate differential extends continuously from smooth scalars
to the actual intrinsic H¹ completion on every compact chart set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartH1_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance chartH1_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def smoothScalarH1Map {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    SmoothScalar (M := M) →ₗ[ℝ] scalarH1 d where
  toFun := smoothScalarToH1 d
  map_add' a b := Subtype.ext ((smoothScalarFirstJet d).map_add a b)
  map_smul' r a := Subtype.ext ((smoothScalarFirstJet d).map_smul r a)

theorem smoothScalarH1Map_dense {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) : DenseRange (smoothScalarH1Map o d) := by
  change Dense (range (smoothScalarH1Map o d))
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro u
  apply closure_mono (s := range (smoothScalarFirstJet d)) ?_ u.property
  rintro v ⟨a, rfl⟩
  exact ⟨smoothScalarToH1 d a, ⟨a, rfl⟩, rfl⟩

def smoothScalarChartDerivative (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    SmoothScalar (M := M) →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun a := (scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _
  map_add' a b := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt (a + b) i),
      MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i),
      MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt b i),
      Lp.coeFn_add ((scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _)
        ((scalarCoordinate_gradient_memLp g c hK hKt b i).toLp _),
      ae_restrict_mem hK.isClosed.measurableSet] with z hab ha hb hsum hz
    rw [hab, hsum]
    simp only [Pi.add_apply]
    rw [ha, hb]
    have hda := (scalarCoordinates_contDiffAt a.property c z (hKt hz)
      (fun j => Fin.elim0 j)).differentiableAt (by simp)
    have hdb := (scalarCoordinates_contDiffAt b.property c z (hKt hz)
      (fun j => Fin.elim0 j)).differentiableAt (by simp)
    change DifferentiableAt ℝ (fun w => a.val ((chartAt FourSpace c).symm w)) z at hda
    change DifferentiableAt ℝ (fun w => b.val ((chartAt FourSpace c).symm w)) z at hdb
    change (fderiv ℝ (fun w => a.val ((chartAt FourSpace c).symm w) +
      b.val ((chartAt FourSpace c).symm w)) z) (coordinateVector i) = _
    rw [fderiv_fun_add hda hdb]
    rfl
  map_smul' r a := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt (r • a) i),
      MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i),
      Lp.coeFn_smul r ((scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _)] with z hra ha hs
    simp only [RingHom.id_apply]
    rw [hra, hs]
    simp only [Pi.smul_apply]
    rw [ha]
    change (fderiv ℝ (r • fun w => a.val ((chartAt FourSpace c).symm w)) z)
      (coordinateVector i) = _
    rw [fderiv_const_smul_field]
    rfl

theorem smoothScalarChartDerivative_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SmoothScalar (M := M),
      ‖smoothScalarChartDerivative g c hK hKt i a‖ ≤ C * ‖smoothScalarH1Map o d a‖ := by
  obtain ⟨A, hA, hAbound⟩ := scalarCoordinate_gradient_sq_le_on_compact g c hK hKt i
  obtain ⟨B, hB, hBbound⟩ := scalarChart_eLpNorm_bound g c hK hKt
  let C := ENNReal.ofReal (Real.sqrt A) * B
  have hC : C ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a
  have hpoint : ∀ᵐ z ∂volume.restrict K,
      ‖partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z‖ ≤
        Real.sqrt A * ‖(scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)‖ := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hn : 0 ≤ (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z) := Real.sqrt_nonneg _
    rw [abs_of_nonneg hn]
    exact scalarCoordinate_gradient_abs_le g c i A hA hAbound a hz
  have hlocal := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (scalarCoordinate_gradient_memLp g c hK hKt a i).aestronglyMeasurable hpoint 2
  have hglobal := hBbound (scalarEnergyRoot g a)
  have he : eLpNorm (scalarEnergyRoot g a) 2 (normalizedVolume g) =
      eLpNorm (scalarEnergyRootL2 g a) 2 (normalizedVolume g) := by
    exact (eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (normalizedVolume g) (scalarEnergyRoot g a))).symm
  have hbound : eLpNorm
      (fun z : FourSpace => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z)
      2 (volume.restrict K) ≤ C * eLpNorm (scalarEnergyRootL2 g a) 2 (normalizedVolume g) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt A) * _ := hlocal
      _ ≤ ENNReal.ofReal (Real.sqrt A) * (B * eLpNorm (scalarEnergyRoot g a) 2
          (normalizedVolume g)) := mul_le_mul' le_rfl hglobal
      _ = _ := by rw [he, mul_assoc]
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (Lp.eLpNorm_ne_top _)) hbound
  have hn : ‖smoothScalarChartDerivative g c hK hKt i a‖ ≤
      C.toReal * ‖scalarEnergyRootL2 g a‖ := by
    change ‖(scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def]
    simpa only [ENNReal.toReal_mul] using hr
  exact hn.trans (mul_le_mul_of_nonneg_left (scalarEnergyRootL2_norm_le g o d a)
    ENNReal.toReal_nonneg)

def scalarH1ChartDerivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (smoothScalarChartDerivative g c hK hKt i).extendOfNorm (smoothScalarH1Map o d)

theorem scalarH1ChartDerivative_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) (a : SmoothScalar (M := M)) :
    scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a) =
      smoothScalarChartDerivative g c hK hKt i a := by
  obtain ⟨C, _, hC⟩ := smoothScalarChartDerivative_bound g o d c hK hKt i
  exact LinearMap.extendOfNorm_eq (smoothScalarH1Map_dense o d) ⟨C, hC⟩ a

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual base L² scalars restrict continuously to compact metric charts.
This map identifies the chart value of every intrinsic H¹ scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartValue_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance chartValue_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem scalarChart_ae_eq (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) {f h : M → ℝ}
    (heq : f =ᵐ[normalizedVolume g] h) :
    (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) =ᵐ[volume.restrict K]
      (fun z : FourSpace => h ((chartAt FourSpace c).symm z)) := by
  obtain ⟨C, _, hC⟩ := scalarChart_eLpNorm_bound g c hK hKt
  have hdiff : (fun x => f x - h x) =ᵐ[normalizedVolume g] 0 :=
    heq.mono (fun _ hx => sub_eq_zero.mpr hx)
  have hn : eLpNorm (fun z : FourSpace =>
      f ((chartAt FourSpace c).symm z) - h ((chartAt FourSpace c).symm z))
      2 (volume.restrict K) = 0 := by
    apply le_antisymm
    · have hb := hC (fun x => f x - h x)
      simpa only [eLpNorm_congr_ae hdiff, eLpNorm_zero, mul_zero] using hb
    · exact zero_le
  have ha := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hn
  exact ha.mono (fun _ hx => sub_eq_zero.mp hx)

private def scalarChartValueLin (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (normalizedVolume g) →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun b := (scalarChartL2_compact g c b hK hKt).toLp _
  map_add' a b := by
    apply Lp.ext
    have hbase := scalarChart_ae_eq g c hK hKt (Lp.coeFn_add a b)
    filter_upwards [MemLp.coeFn_toLp (scalarChartL2_compact g c (a + b) hK hKt),
      MemLp.coeFn_toLp (scalarChartL2_compact g c a hK hKt),
      MemLp.coeFn_toLp (scalarChartL2_compact g c b hK hKt),
      Lp.coeFn_add ((scalarChartL2_compact g c a hK hKt).toLp _)
        ((scalarChartL2_compact g c b hK hKt).toLp _), hbase] with z hab ha hb hs he
    exact hab.trans (he.trans ((congrArg₂ (· + ·) ha hb).symm.trans hs.symm))
  map_smul' r b := by
    apply Lp.ext
    have hbase := scalarChart_ae_eq g c hK hKt (Lp.coeFn_smul r b)
    filter_upwards [MemLp.coeFn_toLp (scalarChartL2_compact g c (r • b) hK hKt),
      MemLp.coeFn_toLp (scalarChartL2_compact g c b hK hKt),
      Lp.coeFn_smul r ((scalarChartL2_compact g c b hK hKt).toLp _), hbase] with z hrb hb hs he
    exact hrb.trans (he.trans ((congrArg (r • ·) hb).symm.trans hs.symm))

private theorem scalarChartValueLin_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, ∀ b : Lp ℝ 2 (normalizedVolume g),
      ‖scalarChartValueLin g c hK hKt b‖ ≤ C * ‖b‖ := by
  obtain ⟨C, _, hC⟩ := scalarChart_norm_bound g c hK hKt
  refine ⟨C, fun b => ?_⟩
  have h := hC b (Lp.memLp b) (scalarChartL2_compact g c b hK hKt)
  simpa only [scalarChartValueLin, LinearMap.coe_mk, AddHom.coe_mk, Lp.toLp_coeFn] using h

def scalarChartValue (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (scalarChartValueLin g c hK hKt).mkContinuousOfExistsBound
    (scalarChartValueLin_bound g c hK hKt)

theorem scalarChartValue_coe (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (b : Lp ℝ 2 (normalizedVolume g)) :
    scalarChartValue g c hK hKt b =ᵐ[volume.restrict K]
      (fun z : FourSpace => b ((chartAt FourSpace c).symm z)) :=
  MemLp.coeFn_toLp (scalarChartL2_compact g c b hK hKt)

def scalarH1ChartValue (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (scalarChartValue g c hK hKt).comp (scalarH1BaseValue g o d)

theorem scalarH1ChartValue_coe (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (u : scalarH1 d)
    (b : Lp ℝ 2 (normalizedVolume g)) (hb : scalarBasePullback g o b = scalarH1Value d u) :
    scalarH1ChartValue g o d c hK hKt u =ᵐ[volume.restrict K]
      (fun z : FourSpace => b ((chartAt FourSpace c).symm z)) := by
  change scalarChartValue g c hK hKt (scalarH1BaseValue g o d u) =ᵐ[_] _
  rw [scalarH1BaseValue_eq g o d u b hb]
  exact scalarChartValue_coe g c hK hKt b

theorem scalarH1ChartValue_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (a : SmoothScalar (M := M)) :
    scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a) =ᵐ[volume.restrict K]
      (fun z : FourSpace => a.val ((chartAt FourSpace c).symm z)) := by
  have h := scalarH1ChartValue_coe g o d c hK hKt (smoothScalarToH1 d a)
    (smoothScalarBaseL2 g a) (scalarBasePullback_smooth g o a)
  exact h.trans (scalarChart_ae_eq g c hK hKt
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local strong minimum principle, using a Euclidean ball
inside one chart and the weak radial barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance localContinuousPositive_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_continuous_no_zero_with_nearby_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hn : ∀ x, 0 ≤ f x)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (c : M) (x y : FourSpace) {R : ℝ} (hR : 0 < R)
    (hchart : closedBall x R ⊆ (chartAt FourSpace c).target)
    (hx : f ((chartAt FourSpace c).symm x) = 0)
    (hy : dist y x < R / 4) (hfy : 0 < f ((chartAt FourSpace c).symm y)) : False := by
  let fc : FourSpace → ℝ := fun z => f ((chartAt FourSpace c).symm z)
  have hsmall : closedBall x (R / 2) ⊆ (chartAt FourSpace c).target :=
    (closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨r, z, hr, hrx, hzy, hfz, hball, hpositive⟩ :=
    scalar_euclidean_positive_contact_ball fc x y hR
      (hf.comp_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hsmall))
      (fun z _ => hn _) hx hy hfy
  let χ : ContDiffBump y :=
    { rIn := 2 * r
      rOut := 3 * r
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target := by
    intro w hw
    apply hchart
    apply mem_closedBall.mpr
    have hdist := dist_triangle w y x
    have hw' : dist w y ≤ 3 * r := mem_closedBall.mp hw
    linarith
  let q := scalarRadialChartFunction c y χ hs
  have hrr : r ^ 2 < χ.rIn ^ 2 := by
    change r ^ 2 < (2 * r) ^ 2
    nlinarith [sq_pos_of_pos hr]
  have hqr : q.val ((chartAt FourSpace c).symm z) = r ^ 2 := by
    have hz : z ∈ closedBall y χ.rIn := by
      apply mem_closedBall.mpr
      change dist z y ≤ 2 * r
      rw [hzy]
      linarith
    rw [scalarRadialChartFunction_on_inner c y χ hs hz]
    rw [← dist_eq_norm, hzy]
  let a := (r / 2) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r ^ 2 := by dsimp [a]; nlinarith [sq_pos_of_pos hr]
  have hqpositive (w : M) (hw : q.val w ≤ a) : 0 < f w := by
    obtain ⟨hwsource, hwball, hwq⟩ := scalarRadialChartFunction_small c y χ hs
      (hw.trans_lt (har.trans hrr))
    have hwinner : chartAt FourSpace c w ∈ ball y r := by
      apply mem_ball.mpr
      rw [dist_eq_norm]
      apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
      rw [← hwq]
      exact hw.trans_lt har
    have hp := hpositive (chartAt FourSpace c w) hwinner
    change 0 < f ((chartAt FourSpace c).symm (chartAt FourSpace c w)) at hp
    rwa [(chartAt FourSpace c).left_inv hwsource] at hp
  let K : Set M := {w | q.val w ≤ a}
  have hK : IsCompact K := (isClosed_le q.property.continuous continuous_const).isCompact
  have hyinner : y ∈ closedBall y χ.rIn := mem_closedBall_self χ.rIn_pos.le
  have hqcenter : q.val ((chartAt FourSpace c).symm y) = 0 := by
    rw [scalarRadialChartFunction_on_inner c y χ hs hyinner]
    simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hKne : K.Nonempty := ⟨(chartAt FourSpace c).symm y, by
    change q.val ((chartAt FourSpace c).symm y) ≤ a
    rw [hqcenter]
    exact ha.le⟩
  obtain ⟨w, hw, hwmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  have hδ : 0 < f w := hqpositive w hw
  have hinner : ∀ v, q.val v ≤ a → f w ≤ f v := fun v hv => hwmin hv
  let R₁ := (3 * r / 2) ^ 2
  have hrR : r ^ 2 < R₁ := by dsimp [R₁]; nlinarith [sq_pos_of_pos hr]
  have hRr : R₁ < χ.rIn ^ 2 := by
    change (3 * r / 2) ^ 2 < (2 * r) ^ 2
    nlinarith [sq_pos_of_pos hr]
  obtain ⟨η, hη, hgrad⟩ : ∃ η : ℝ, 0 < η ∧ ∀ e : FrameBundle g,
      a ≤ q.val e.base → q.val e.base ≤ R₁ →
        η ≤ ∑ i, scalarGradient g q.val e i ^ 2 :=  scalar_positive_annular_gradient_bound g q
    ⟨frameAt g ((chartAt FourSpace c).symm z), by
      change a ≤ q.val ((chartAt FourSpace c).symm z) ∧
        q.val ((chartAt FourSpace c).symm z) ≤ R₁
      rw [hqr]
      exact ⟨har.le, hrR.le⟩⟩
    (fun e he₁ he₂ => scalar_radial_annulus_gradient_pos g c y χ hs ha hRr e he₁ he₂)
  obtain ⟨B, hB, hlap⟩ := scalar_laplacian_uniform_upper g q
  exact scalarH1_no_zero_inside_radial_barrier g o d u F heq f hf hrep q
    hη hB hδ hn (scalarRadialChartFunction_nonneg c y χ hs) hinner hgrad hlap hsource
    ((chartAt FourSpace c).symm z) (by rw [hqr]; exact hrR) hfz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate integration by parts only needs smoothness near the compact
test support. Thus the arbitrary values of an inverse chart outside its
target never enter the local weak derivative identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

private theorem scalar_local_product_integrable (f q : FourSpace → ℝ)
    (hq : Continuous q) (hc : HasCompactSupport q)
    (hf : ∀ z ∈ tsupport q, ContinuousAt f z) :
    Integrable (fun z => f z * q z) volume := by
  have ht : tsupport (fun z => f z * q z) ⊆ tsupport q :=
    tsupport_mul_subset_right
  have hp : Continuous (fun z => f z * q z) := by
    apply continuous_of_tsupport
    intro z hz
    exact (hf z (ht hz)).mul hq.continuousAt
  exact hp.integrable_of_hasCompactSupport hc.mul_left

theorem scalar_local_integration_by_parts (f ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hf : ∀ z ∈ tsupport ψ, ContDiffAt ℝ ∞ f z) (i : Fin 4) :
    (∫ z, f z * partialDeriv ψ i z) = -(∫ z, partialDeriv f i z * ψ z) := by
  have hDψ : ContDiff ℝ ∞ (fun z => partialDeriv ψ i z) :=
    (hψ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))
  have hsupport : tsupport (fun z => partialDeriv ψ i z) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ (coordinateVector i)
  have hcD : HasCompactSupport (fun z => partialDeriv ψ i z) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hDfψ : Integrable (fun z => partialDeriv f i z * ψ z) volume := by
    apply scalar_local_product_integrable _ ψ hψ.continuous hc
    intro z hz
    exact (((hf z hz).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).continuousAt
  have hfDψ : Integrable (fun z => f z * partialDeriv ψ i z) volume :=
    scalar_local_product_integrable f _ hDψ.continuous hcD
      (fun z hz => (hf z (hsupport hz)).continuousAt)
  have hfψ : Integrable (fun z => f z * ψ z) volume :=
    scalar_local_product_integrable f ψ hψ.continuous hc
      (fun z hz => (hf z hz).continuousAt)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDfψ hfDψ hfψ
    (fun z hz => (hf z hz).differentiableAt (by simp))
    (fun z _ => hψ.differentiable (by simp) z)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_chart_integration_by_parts (a : SmoothScalar (M := M)) (c : M)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    (∫ z, a.val ((chartAt FourSpace c).symm z) * partialDeriv ψ i z) =
      -(∫ z, partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z * ψ z) :=
  scalar_local_integration_by_parts _ ψ hψ hc
    (fun z hz => scalarCoordinates_contDiffAt a.property c z (hs hz) (fun j => Fin.elim0 j)) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local strong minimum principle, using a Euclidean ball
inside one chart and the weak radial barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance localPositive_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_no_zero_with_nearby_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hfd : ∀ (i : Fin 4) (e : FrameBundle g), DifferentiableAt ℝ
      (fun t : ℝ => f (((d.toMetricGreenData.flow i).map t) e).base) 0)
    (hn : ∀ x, 0 ≤ f x)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (c : M) (x y : FourSpace) {R : ℝ} (hR : 0 < R)
    (hchart : closedBall x R ⊆ (chartAt FourSpace c).target)
    (hx : f ((chartAt FourSpace c).symm x) = 0)
    (hy : dist y x < R / 4) (hfy : 0 < f ((chartAt FourSpace c).symm y)) : False := by
  let fc : FourSpace → ℝ := fun z => f ((chartAt FourSpace c).symm z)
  have hsmall : closedBall x (R / 2) ⊆ (chartAt FourSpace c).target :=
    (closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨r, z, hr, hrx, hzy, hfz, hball, hpositive⟩ :=
    scalar_euclidean_positive_contact_ball fc x y hR
      (hf.comp_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hsmall))
      (fun z _ => hn _) hx hy hfy
  let χ : ContDiffBump y :=
    { rIn := 2 * r
      rOut := 3 * r
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target := by
    intro w hw
    apply hchart
    apply mem_closedBall.mpr
    have hdist := dist_triangle w y x
    have hw' : dist w y ≤ 3 * r := mem_closedBall.mp hw
    linarith
  let q := scalarRadialChartFunction c y χ hs
  have hrr : r ^ 2 < χ.rIn ^ 2 := by
    change r ^ 2 < (2 * r) ^ 2
    nlinarith [sq_pos_of_pos hr]
  have hqr : q.val ((chartAt FourSpace c).symm z) = r ^ 2 := by
    have hz : z ∈ closedBall y χ.rIn := by
      apply mem_closedBall.mpr
      change dist z y ≤ 2 * r
      rw [hzy]
      linarith
    rw [scalarRadialChartFunction_on_inner c y χ hs hz]
    rw [← dist_eq_norm, hzy]
  let a := (r / 2) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r ^ 2 := by dsimp [a]; nlinarith [sq_pos_of_pos hr]
  have hqpositive (w : M) (hw : q.val w ≤ a) : 0 < f w := by
    obtain ⟨hwsource, hwball, hwq⟩ := scalarRadialChartFunction_small c y χ hs
      (hw.trans_lt (har.trans hrr))
    have hwinner : chartAt FourSpace c w ∈ ball y r := by
      apply mem_ball.mpr
      rw [dist_eq_norm]
      apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
      rw [← hwq]
      exact hw.trans_lt har
    have hp := hpositive (chartAt FourSpace c w) hwinner
    change 0 < f ((chartAt FourSpace c).symm (chartAt FourSpace c w)) at hp
    rwa [(chartAt FourSpace c).left_inv hwsource] at hp
  let K : Set M := {w | q.val w ≤ a}
  have hK : IsCompact K := (isClosed_le q.property.continuous continuous_const).isCompact
  have hyinner : y ∈ closedBall y χ.rIn := mem_closedBall_self χ.rIn_pos.le
  have hqcenter : q.val ((chartAt FourSpace c).symm y) = 0 := by
    rw [scalarRadialChartFunction_on_inner c y χ hs hyinner]
    simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hKne : K.Nonempty := ⟨(chartAt FourSpace c).symm y, by
    change q.val ((chartAt FourSpace c).symm y) ≤ a
    rw [hqcenter]
    exact ha.le⟩
  obtain ⟨w, hw, hwmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  have hδ : 0 < f w := hqpositive w hw
  have hinner : ∀ v, q.val v ≤ a → f w ≤ f v := fun v hv => hwmin hv
  obtain ⟨η, hη, hgrad⟩ := scalar_positive_annular_gradient_bound g q
    ⟨frameAt g ((chartAt FourSpace c).symm z), by
      change a ≤ q.val ((chartAt FourSpace c).symm z) ∧
        q.val ((chartAt FourSpace c).symm z) ≤ r ^ 2
      rw [hqr]
      exact ⟨har.le, le_rfl⟩⟩
    (fun e he₁ he₂ => scalar_radial_annulus_gradient_pos g c y χ hs ha hrr e he₁ he₂)
  obtain ⟨B, hB, hlap⟩ := scalar_laplacian_uniform_upper g q
  exact scalarH1_no_zero_at_radial_contact g o d u F heq f hf hrep hfd q
    har hη hB hδ hn (scalarRadialChartFunction_nonneg c y χ hs) hinner hgrad hlap hsource
    ((chartAt FourSpace c).symm z) hqr hfz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact transformation of the geometric chart Laplacian under the
constructed frozen-frame rescaling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarRescaledOperator (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (ψ : FourSpace → ℝ) (y : FourSpace) : ℝ :=
  scalarPrincipalContraction (scalarRescaledPrincipal g c z₀ r y)
    (scalarPartialMatrix ψ y) +
    scalarRescaledDrift g c z₀ r y ⬝ᵥ scalarPartialVector ψ y

theorem scalarRescaledOperator_eq_zero_off_tsupport (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (ψ : FourSpace → ℝ) {y : FourSpace}
    (hy : y ∉ tsupport ψ) : scalarRescaledOperator g c z₀ r ψ y = 0 := by
  have hfirst (i : Fin 4) : partialDeriv ψ i y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy
      (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h))
  have hsecond (i j : Fin 4) : partialDeriv (fun z => partialDeriv ψ j z) i y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy
      (tsupport_fderiv_apply_subset ℝ (coordinateVector j)
        (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h)))
  simp only [scalarRescaledOperator, scalarPrincipalContraction, scalarPartialMatrix,
    scalarPartialVector, dotProduct, hfirst, hsecond, mul_zero, Finset.sum_const_zero, add_zero]

private theorem scalarContraction_smul (s : ℝ) (H Q : Mat4) :
    scalarPrincipalContraction (s • H) Q = s * scalarPrincipalContraction H Q := by
  simp only [scalarPrincipalContraction, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem scalarRescaling_principal (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (z : FourSpace) :
    r ^ 2 • ((r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) *
      (metricInChart g c z)⁻¹ * (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹)ᵀ) =
      frozenScalarPrincipal g c z₀ z := by
  rw [frozenScalarPrincipal_eq_conjugate]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h : r ^ 2 * (r⁻¹ * r⁻¹) = 1 := by field_simp [hr]
  rw [h, one_smul]

theorem scalarRescaling_drift (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (y : FourSpace) :
    r ^ 2 • ((r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) *ᵥ
      scalarChartDrift g c (scalarRescaledPoint g c z₀ r y)) =
        -scalarRescaledDrift g c z₀ r y := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.smul_apply, Pi.neg_apply, scalarRescaledDrift, scalarFrozenDrift,
    scalarChartDrift, mul_assoc]
  rw [← Finset.mul_sum]
  have h : r ^ 2 * r⁻¹ = r := by field_simp [hr]
  simp only [← mul_assoc, h, mul_neg, neg_neg]

theorem scalarRescaledOperator_eq_chart (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (y : FourSpace) :
    r ^ 2 * scalarChartOperator g c
      (fun z => ψ ((scalarRescalingLinearEquiv g c z₀ r hr).symm (z - z₀)))
      (scalarRescaledPoint g c z₀ r y) = scalarRescaledOperator g c z₀ r ψ y := by
  let C : Mat4 := r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹
  let q := -((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C z₀)
  have he : (fun z => ψ ((scalarRescalingLinearEquiv g c z₀ r hr).symm (z - z₀))) =
      fun z => ψ (scalarAffineMap C q z) := by
    funext z
    rw [scalarRescaling_inverse_affine]
  have hy : scalarAffineMap C q (scalarRescaledPoint g c z₀ r y) = y := by
    rw [← scalarRescaling_inverse_affine g c z₀ r hr,
      ← scalarRescalingLinearEquiv_apply g c z₀ r hr y, add_sub_cancel_right]
    exact ContinuousLinearEquiv.symm_apply_apply _ y
  rw [he, scalarChartOperator_affine g c C q _ ψ hψ, hy, mul_sub,
    ← scalarContraction_smul, scalarRescaling_principal g c z₀ r hr]
  have hd := congrArg (fun v : Fin 4 → ℝ => v ⬝ᵥ scalarPartialVector ψ y)
    (scalarRescaling_drift g c z₀ r hr y)
  rw [smul_dotProduct, neg_dotProduct] at hd
  simp only [smul_eq_mul] at hd
  change scalarPrincipalContraction (scalarRescaledPrincipal g c z₀ r y)
    (scalarPartialMatrix ψ y) - _ = _
  rw [hd]
  exact sub_neg_eq_add _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The extended coordinate derivative is the weak derivative of the actual
chart representative, verified against genuine compact smooth tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def scalarCompactTestL2 (K : Set FourSpace) (ψ : FourSpace → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : Lp ℝ 2 (volume.restrict K) :=
  ((hψ.memLp_of_hasCompactSupport hc).restrict K).toLp ψ

theorem scalarCompactTestL2_coe (K : Set FourSpace) (ψ : FourSpace → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    scalarCompactTestL2 K ψ hψ hc =ᵐ[volume.restrict K] ψ :=
  MemLp.coeFn_toLp _

def scalarCompactDerivativeL2 (K : Set FourSpace) (ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (i : Fin 4) :
    Lp ℝ 2 (volume.restrict K) :=
  scalarCompactTestL2 K (fun z => partialDeriv ψ i z)
    (((hψ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))).continuous)
    (hc.fderiv_apply ℝ (coordinateVector i))

private theorem scalar_real_L2_pairing {K : Set FourSpace}
    (u v : Lp ℝ 2 (volume.restrict K)) :
    inner ℝ u v = ∫ z in K, u z * v z := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartWeak_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarChart_smooth_weak_derivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (a : SmoothScalar (M := M))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ K) (i : Fin 4) :
    inner ℝ (scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a))
      (scalarCompactDerivativeL2 K ψ hψ hc i) =
    -inner ℝ (scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a))
      (scalarCompactTestL2 K ψ hψ.continuous hc) := by
  have hval := scalarH1ChartValue_smooth g o d c hK hKt a
  have hgrad : scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a) =ᵐ[volume.restrict K]
      (fun z => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) := by
    rw [scalarH1ChartDerivative_smooth]
    exact MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i)
  have htest := scalarCompactTestL2_coe K ψ hψ.continuous hc
  have hDtest : scalarCompactDerivativeL2 K ψ hψ hc i =ᵐ[volume.restrict K]
      (fun z => partialDeriv ψ i z) := scalarCompactTestL2_coe ..
  have hDsupport : tsupport (fun z => partialDeriv ψ i z) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs
  have hleft : (∫ z in K, a.val ((chartAt FourSpace c).symm z) * partialDeriv ψ i z) =
      ∫ z, a.val ((chartAt FourSpace c).symm z) * partialDeriv ψ i z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hDsupport h)), mul_zero]
  have hright : (∫ z in K,
      partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z * ψ z) =
      ∫ z, partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
  rw [scalar_real_L2_pairing, scalar_real_L2_pairing]
  have hl := integral_congr_ae (hval.mul hDtest)
  have hr := integral_congr_ae (hgrad.mul htest)
  simp only [Pi.mul_apply] at hl hr
  rw [hl, hr, hleft, hright]
  exact scalar_chart_integration_by_parts a c ψ hψ hc (hs.trans hKt) i

theorem scalarH1Chart_weak_derivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (u : scalarH1 d)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ K) (i : Fin 4) :
    inner ℝ (scalarH1ChartValue g o d c hK hKt u)
      (scalarCompactDerivativeL2 K ψ hψ hc i) =
    -inner ℝ (scalarH1ChartDerivative g o d c hK hKt i u)
      (scalarCompactTestL2 K ψ hψ.continuous hc) := by
  have hclosed : IsClosed {v : scalarH1 d |
      inner ℝ (scalarH1ChartValue g o d c hK hKt v)
        (scalarCompactDerivativeL2 K ψ hψ hc i) =
      -inner ℝ (scalarH1ChartDerivative g o d c hK hKt i v)
        (scalarCompactTestL2 K ψ hψ.continuous hc)} :=
    isClosed_eq ((scalarH1ChartValue g o d c hK hKt).continuous.inner continuous_const)
      ((scalarH1ChartDerivative g o d c hK hKt i).continuous.inner continuous_const).neg
  exact (smoothScalarH1Map_dense o d).induction_on u hclosed
    (fun a => scalarChart_smooth_weak_derivative g o d c hK hKt a ψ hψ hc hs i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strict positivity of a nonzero nonnegative weak supersolution on the
connected manifold, from the actual chart contact-ball argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

local instance continuousStrongMin_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_continuous_strong_minimum (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hn : ∀ x, 0 ≤ f x)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (hne : ∃ x, 0 < f x) : ∀ x, 0 < f x := by
  let U := {x | 0 < f x}
  have hopen : IsOpen U := isOpen_lt continuous_const hf
  have hclosed : IsClosed U := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxzero : f x = 0 := le_antisymm (le_of_not_gt hx) (hn x)
    let c := chartAt FourSpace x
    let z := c x
    have hxs : x ∈ c.source := mem_chart_source FourSpace x
    have hzt : z ∈ c.target := c.map_source hxs
    obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp c.open_target z hzt
    have hRc : closedBall z (R / 2) ⊆ c.target := by
      intro y hy
      apply hRt
      apply mem_ball.mpr
      have := mem_closedBall.mp hy
      linarith
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ dist (c y) z < (R / 2) / 4 := by
      have hc := (c.continuousAt hxs).tendsto.eventually
        (ball_mem_nhds z (show 0 < (R / 2) / 4 by positivity))
      filter_upwards [c.open_source.mem_nhds hxs, hc] with y hy hz
      exact ⟨hy, hz⟩
    filter_upwards [hnear] with y hy
    change ¬ 0 < f y
    intro hfy
    apply scalarH1_continuous_no_zero_with_nearby_positive g o d u F heq f hf hrep hn hsource
      x z (c y) (half_pos hR) hRc
    · change f (c.symm (c x)) = 0
      rwa [c.left_inv hxs]
    · exact hy.2
    · change 0 < f (c.symm (c y))
      rwa [c.left_inv hy.1]
  have heqU : U = univ := (show IsClopen U from ⟨hclosed, hopen⟩).eq_univ hne
  intro x
  have hx : x ∈ U := heqU ▸ mem_univ x
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical Euclidean H1-to-L4 estimate needed by the compact
four-dimensional scalar minimization. The constant here is not sharp;
sharpness on the manifold comes from the nonlinear rigidity argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal NNReal

noncomputable section

namespace ScalarEuclideanSobolev

local notation "V" => FourSpace

def constant : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) 2

theorem critical_estimate {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    eLpNorm f 4 volume ≤ constant * eLpNorm (fderiv ℝ f) 2 volume := by
  simpa [constant] using
    (eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure V) hf hc
      (p := 2) (p' := 4) (by norm_num) (by simp [FourSpace]) (by
        norm_num [FourSpace]))

def toL4 (f : ↥(Euclidean.C1c (E := V))) : Lp ℝ 4 (volume : Measure V) :=
  (f.property.1.continuous.memLp_of_hasCompactSupport f.property.2).toLp f.val

theorem toL4_coe (f : ↥(Euclidean.C1c (E := V))) :
    (toL4 f : V → ℝ) =ᵐ[volume] f.val :=
  MemLp.coeFn_toLp _

def toL4Linear : ↥(Euclidean.C1c (E := V)) →ₗ[ℝ] Lp ℝ 4 (volume : Measure V) where
  toFun := toL4
  map_add' f h := by
    apply Lp.ext
    filter_upwards [toL4_coe (f + h), toL4_coe f, toL4_coe h,
      Lp.coeFn_add (toL4 f) (toL4 h)] with x hsum hf hh hLp
    rw [hsum, hLp]
    change f.val x + h.val x = (toL4 f : V → ℝ) x + (toL4 h : V → ℝ) x
    rw [hf, hh]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [toL4_coe (r • f), toL4_coe f,
      Lp.coeFn_smul r (toL4 f)] with x hrf hf hLp
    simp only [RingHom.id_apply]
    rw [hrf, hLp]
    change r * f.val x = r * (toL4 f : V → ℝ) x
    rw [hf]

theorem gradient_eLpNorm {f : V → ℝ} (hf : ContDiff ℝ 1 f) :
    eLpNorm (Euclidean.grad f) 2 volume = eLpNorm (fderiv ℝ f) 2 volume := by
  apply eLpNorm_congr_norm_ae (Euclidean.continuous_grad hf).aestronglyMeasurable
    (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
  filter_upwards with x
  exact (InnerProductSpace.toDual ℝ V).symm.norm_map (fderiv ℝ f x)

/-- The gradient in the existing Lebesgue measurable space of `FourSpace`. -/
def gradientL2 (f : ↥(Euclidean.C1c (E := V))) : Lp V 2 (volume : Measure V) :=
  ((Euclidean.continuous_grad f.property.1).memLp_of_hasCompactSupport
    (Euclidean.hasCompactSupport_grad f.property.2)).toLp _

theorem toL4_bound (f : ↥(Euclidean.C1c (E := V))) :
    ‖toL4Linear f‖ ≤ (constant : ℝ) * ‖gradientL2 f‖ := by
  change ‖toL4 f‖ ≤ (constant : ℝ) * ‖gradientL2 f‖
  have h := critical_estimate f.property.1 f.property.2
  rw [← gradient_eLpNorm f.property.1] at h
  have ht : constant * eLpNorm (Euclidean.grad f.val) 2 volume ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (((Euclidean.continuous_grad f.property.1).memLp_of_hasCompactSupport
        (Euclidean.hasCompactSupport_grad f.property.2)) :
          MemLp (Euclidean.grad f.val) 2 volume).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono ht h
  simpa only [toL4, gradientL2, Lp.norm_toLp,
    ENNReal.toReal_mul, ENNReal.coe_toReal] using hr

end ScalarEuclideanSobolev

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strict positivity of a nonzero nonnegative weak supersolution on the
connected manifold, from the actual chart contact-ball argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

local instance strongMin_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_strong_minimum (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hfd : ∀ (i : Fin 4) (e : FrameBundle g), DifferentiableAt ℝ
      (fun t : ℝ => f (((d.toMetricGreenData.flow i).map t) e).base) 0)
    (hn : ∀ x, 0 ≤ f x)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (hne : ∃ x, 0 < f x) : ∀ x, 0 < f x := by
  let U := {x | 0 < f x}
  have hopen : IsOpen U := isOpen_lt continuous_const hf
  have hclosed : IsClosed U := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxzero : f x = 0 := le_antisymm (le_of_not_gt hx) (hn x)
    let c := chartAt FourSpace x
    let z := c x
    have hxs : x ∈ c.source := mem_chart_source FourSpace x
    have hzt : z ∈ c.target := c.map_source hxs
    obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp c.open_target z hzt
    have hRc : closedBall z (R / 2) ⊆ c.target := by
      intro y hy
      apply hRt
      apply mem_ball.mpr
      have := mem_closedBall.mp hy
      linarith
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ dist (c y) z < (R / 2) / 4 := by
      have hc := (c.continuousAt hxs).tendsto.eventually
        (ball_mem_nhds z (show 0 < (R / 2) / 4 by positivity))
      filter_upwards [c.open_source.mem_nhds hxs, hc] with y hy hz
      exact ⟨hy, hz⟩
    filter_upwards [hnear] with y hy
    change ¬ 0 < f y
    intro hfy
    apply scalarH1_no_zero_with_nearby_positive g o d u F heq f hf hrep hfd hn hsource
      x z (c y) (half_pos hR) hRc
    · change f (c.symm (c x)) = 0
      rwa [c.left_inv hxs]
    · exact hy.2
    · change 0 < f (c.symm (c y))
      rwa [c.left_inv hy.1]
  have heqU : U = univ := (show IsClopen U from ⟨hclosed, hopen⟩).eq_univ hne
  intro x
  have hx : x ∈ U := heqU ▸ mem_univ x
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! A C1 scalar has the first-order regularity along the actual frame
flows needed by the strong minimum principle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalarC1_differentiable_along_flow (d : ParallelMetricData g μ)
    (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 1 f) (i : Fin 4)
    (e : FrameBundle g) : DifferentiableAt ℝ
      (fun t : ℝ => f (((d.toMetricGreenData.flow i).map t) e).base) 0 := by
  let γ := fun t : ℝ => (d.flow i).map t e
  let c := (γ 0).base
  have hsource : c ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have htarget : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source hsource
  have hc : ContDiffAt ℝ 1 (fun z => f ((chartAt FourSpace c).symm z))
      (chartAt FourSpace c c) :=
    (hf.contMDiffAt.comp _ (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas c) htarget)).contDiffAt
  have hp := (d.parallelCurve i 0 e).velocity
  have hd := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hp
  have heq : (fun t : ℝ => f (γ t).base) =ᶠ[𝓝 0]
      (fun t : ℝ => f ((chartAt FourSpace c).symm (chartAt FourSpace c (γ t).base))) := by
    have hn := ((continuous_frameBase g).continuousAt.comp
      (d.curve_continuous i e).continuousAt).eventually
        ((chartAt FourSpace c).open_source.mem_nhds hsource)
    filter_upwards [hn] with t ht
    change (γ t).base ∈ (chartAt FourSpace c).source at ht
    rw [(chartAt FourSpace c).left_inv ht]
  exact hd.differentiableAt.congr_of_eventuallyEq heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate form of the Euclidean Sobolev estimate. The finite sum of
the four partial L² norms controls the gradient L² norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal

noncomputable section

namespace ScalarEuclideanSobolev

theorem fderiv_norm_le_sum_partial (f : FourSpace → ℝ) (z : FourSpace) :
    ‖fderiv ℝ f z‖ ≤ ∑ i : Fin 4, ‖partialDeriv f i z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))).mp
  have he := (EuclideanSpace.basisFun (Fin 4) ℝ).norm_dual (fderiv ℝ f z)
  have hb (i : Fin 4) : (EuclideanSpace.basisFun (Fin 4) ℝ) i = coordinateVector i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [hb] at he
  change ‖fderiv ℝ f z‖ ^ 2 = ∑ i : Fin 4, (partialDeriv f i z) ^ 2 at he
  rw [he]
  simpa only [Real.norm_eq_abs, sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin 4 => ‖partialDeriv f i z‖) (fun i _ => norm_nonneg _))

theorem continuous_partial {f : FourSpace → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 4) :
    Continuous (partialDeriv f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

def partialL2 (f : ↥(Euclidean.C1c (E := FourSpace))) (i : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  ((continuous_partial f.property.1 i).memLp_of_hasCompactSupport
    (f.property.2.fderiv_apply ℝ (coordinateVector i))).toLp _

theorem partialL2_coe (f : ↥(Euclidean.C1c (E := FourSpace))) (i : Fin 4) :
    partialL2 f i =ᵐ[volume] partialDeriv f.val i := MemLp.coeFn_toLp _

theorem gradientL2_norm_le_sum (f : ↥(Euclidean.C1c (E := FourSpace))) :
    ‖gradientL2 f‖ ≤ ∑ i : Fin 4, ‖partialL2 f i‖ := by
  have hb : eLpNorm (fderiv ℝ f.val) 2 volume ≤
      ∑ i : Fin 4, eLpNorm (partialDeriv f.val i) 2 volume := by
    calc
      _ ≤ eLpNorm (fun z => ∑ i : Fin 4, ‖partialDeriv f.val i z‖) 2 volume :=
        eLpNorm_mono_real (f.property.1.continuous_fderiv one_ne_zero).aestronglyMeasurable
          (fderiv_norm_le_sum_partial f.val)
      _ ≤ ∑ i : Fin 4, eLpNorm (fun z => ‖partialDeriv f.val i z‖) 2 volume := by
        have he : (fun z => ∑ i : Fin 4, ‖partialDeriv f.val i z‖) =
            (∑ i : Fin 4, fun z => ‖partialDeriv f.val i z‖) := by
          funext z
          simp only [Finset.sum_apply]
        rw [he]
        exact (eLpNorm_sum_le (μ := (volume : Measure FourSpace)) (p := 2)
            (f := fun i : Fin 4 => fun z => ‖partialDeriv f.val i z‖)
            (s := Finset.univ) (by norm_num))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact eLpNorm_norm _ (continuous_partial f.property.1 i).aestronglyMeasurable
  have ht : (∑ i : Fin 4, eLpNorm (partialDeriv f.val i) 2 volume) ≠ (∞ : ℝ≥0∞) := by
    apply ne_of_lt
    exact ENNReal.sum_lt_top.mpr (fun i _ =>
      ((continuous_partial f.property.1 i).memLp_of_hasCompactSupport
        (f.property.2.fderiv_apply ℝ (coordinateVector i))).eLpNorm_lt_top)
  have hr := ENNReal.toReal_mono ht hb
  rw [← gradient_eLpNorm f.property.1] at hr
  simpa only [gradientL2, partialL2, Lp.norm_toLp, ENNReal.toReal_sum
    (fun i _ => ((continuous_partial f.property.1 i).memLp_of_hasCompactSupport
      (f.property.2.fderiv_apply ℝ (coordinateVector i))).eLpNorm_ne_top)] using hr

theorem toL4_bound_partials (f : ↥(Euclidean.C1c (E := FourSpace))) :
    ‖toL4Linear f‖ ≤ (constant : ℝ) * ∑ i : Fin 4, ‖partialL2 f i‖ :=
  (toL4_bound f).trans (mul_le_mul_of_nonneg_left (gradientL2_norm_le_sum f)
    (NNReal.coe_nonneg _))

end ScalarEuclideanSobolev

end
end PositiveEinsteinFour.Geometry
end


section

/-! Multiplying a local L² representative by a compact cutoff gives a
genuine global L² function, independent of its values off the local set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

theorem scalarLocalL2_product_memLp {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) :
    MemLp (fun z => χ z * f z) 2 volume := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  have hp : MemLp (fun z => χ z * f z) 2 (volume.restrict K) := by
    apply (Lp.memLp f).of_le_mul (c := C)
      (hχ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards with z
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC (χ z) (mem_range_self z)) (norm_nonneg _)
  have heq : K.indicator (fun z => χ z * f z) = (fun z => χ z * f z) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hs ((subset_tsupport χ) (left_ne_zero_of_mul hz))
  rw [← heq]
  exact (memLp_indicator_iff_restrict hK).mpr hp

def scalarLocalL2Product {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) : Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarLocalL2_product_memLp hK χ hχ hc hs f).toLp _

theorem scalarLocalL2Product_coe {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) :
    scalarLocalL2Product hK χ hχ hc hs f =ᵐ[volume] (fun z => χ z * f z) :=
  MemLp.coeFn_toLp (scalarLocalL2_product_memLp hK χ hχ hc hs f)

theorem scalarLocalL2Product_integral {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) (ψ : FourSpace → ℝ) :
    (∫ z, scalarLocalL2Product hK χ hχ hc hs f z * ψ z) =
      ∫ z in K, χ z * f z * ψ z := by
  have he := integral_congr_ae ((scalarLocalL2Product_coe hK χ hχ hc hs f).mul
    (Filter.EventuallyEq.rfl (f := ψ)))
  simp only [Pi.mul_apply] at he
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht)), zero_mul, zero_mul]

theorem scalarLocalL2_mul_integrable {K : Set FourSpace}
    (f : Lp ℝ 2 (volume.restrict K)) (q : FourSpace → ℝ)
    (hq : Continuous q) (hc : HasCompactSupport q) :
    Integrable (fun z => f z * q z) (volume.restrict K) :=
  (Lp.memLp f).integrable_mul ((hq.memLp_of_hasCompactSupport (p := 2) hc).restrict K)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

private def h2Bump : ContDiffBump (0 : V) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def h2Cutoff (n : ℕ) (x : V) : ℝ :=
  h2Bump (((n : ℝ) + 1)⁻¹ • x)

private theorem h2Cutoff_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (h2Cutoff n) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : V => h2Bump (((n : ℝ) + 1)⁻¹ • x))
  exact h2Bump.contDiff.comp (show ContDiff ℝ (⊤ : ℕ∞)
    (fun x : V => ((n : ℝ) + 1)⁻¹ • x) by fun_prop)

private theorem h2Cutoff_compact (n : ℕ) : HasCompactSupport (h2Cutoff n) :=
  h2Bump.hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

private def h2BumpDerivativeBound : ℝ :=
  SchwartzMap.seminorm ℝ 0 0
    (SchwartzMap.fderivCLM ℝ V ℝ (h2Bump.hasCompactSupport.toSchwartzMap h2Bump.contDiff))

private theorem h2BumpDerivativeBound_nonneg : 0 ≤ h2BumpDerivativeBound := by
  exact apply_nonneg _ _

private theorem h2Cutoff_derivative (n : ℕ) (x : V) :
    ‖fderiv ℝ (h2Cutoff n) x‖ ≤ h2BumpDerivativeBound := by
  have hd : DifferentiableAt ℝ h2Bump (((n : ℝ) + 1)⁻¹ • x) :=
    h2Bump.contDiff.differentiable_one |>.differentiableAt
  change ‖fderiv ℝ (fun y : V => h2Bump (((n : ℝ) + 1)⁻¹ • y)) x‖ ≤ _
  have hchain : fderiv ℝ (fun y : V => h2Bump (((n : ℝ) + 1)⁻¹ • y)) x =
      (fderiv ℝ h2Bump (((n : ℝ) + 1)⁻¹ • x)).comp
        (fderiv ℝ (fun y : V => ((n : ℝ) + 1)⁻¹ • y) x) := by
    simpa only [Function.comp_def] using fderiv_comp x hd
      ((differentiable_id.const_smul ((n : ℝ) + 1)⁻¹).differentiableAt)
  rw [hchain]
  calc
    _ ≤ ‖fderiv ℝ h2Bump (((n : ℝ) + 1)⁻¹ • x)‖ *
        ‖fderiv ℝ (fun y : V => ((n : ℝ) + 1)⁻¹ • y) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ h2BumpDerivativeBound * 1 := by
      apply mul_le_mul
      · exact SchwartzMap.norm_le_seminorm ℝ
          (SchwartzMap.fderivCLM ℝ V ℝ
            (h2Bump.hasCompactSupport.toSchwartzMap h2Bump.contDiff)) _
      · have hi : HasFDerivAt (fun y : V => ((n : ℝ) + 1)⁻¹ • y)
            (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ V) x :=
          by
          simpa only [Pi.smul_apply, id_eq] using!
            ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul ((n : ℝ) + 1)⁻¹)
        rw [hi.fderiv, norm_smul, ContinuousLinearMap.norm_id, mul_one,
          Real.norm_eq_abs, abs_inv, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
        exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      · positivity
      · exact h2BumpDerivativeBound_nonneg
    _ = _ := mul_one _

private theorem h2Cutoff_tendsto (x : V) :
    Tendsto (fun n => h2Cutoff n x) atTop (𝓝 1) := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hx := h2Bump.continuous.continuousAt.tendsto.comp (hr.smul_const x)
  have hz : h2Bump (0 : V) = 1 := h2Bump.one_of_mem_closedBall (by simp [h2Bump])
  simpa only [h2Cutoff, Function.comp_def, zero_smul, hz] using hx

private theorem h2_operator_norm (L : V →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ i : Fin 4, ‖L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hx := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hc (i : Fin 4) : |x i| ≤ ‖x‖ := by
    simpa only [EuclideanSpace.inner_basisFun_real,
      (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one, mul_one] using
      abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin 4) ℝ i)
  calc
    ‖L x‖ = ‖∑ i : Fin 4, (x i) • L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := by
      congr 1
      conv_lhs => rw [← hx]
      simp
    _ ≤ ∑ i : Fin 4, ‖(x i) • L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 4, ‖x‖ * ‖L (EuclideanSpace.basisFun (Fin 4) ℝ i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

private theorem h2_cutoff_fderiv_bound (f : 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    ‖fderiv ℝ (fun y => h2Cutoff n y • f y) x‖ ≤
      h2BumpDerivativeBound * ‖f x‖ +
        ∑ i : Fin 4, ‖(∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f) x‖ := by
  rw [fderiv_fun_smul ((h2Cutoff_smooth n).of_le (by simp) |>.differentiable_one |>.differentiableAt)
    ((f.smooth 1).differentiable_one |>.differentiableAt)]
  rw [add_comm]
  calc
    _ ≤ ‖(fderiv ℝ (h2Cutoff n) x).smulRight (f x)‖ +
        ‖h2Cutoff n x • fderiv ℝ f x‖ := norm_add_le _ _
    _ ≤ h2BumpDerivativeBound * ‖f x‖ + 1 * ‖fderiv ℝ f x‖ := by
      simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (h2Cutoff_derivative n x) (norm_nonneg _)
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        change |h2Bump (((n : ℝ) + 1)⁻¹ • x)| ≤ 1
        rw [abs_of_nonneg h2Bump.nonneg]
        exact h2Bump.le_one
    _ ≤ _ := by
      rw [one_mul]
      apply add_le_add le_rfl
      simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
        h2_operator_norm (fderiv ℝ f x)

private theorem h2_compact_critical (f : V → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    eLpNorm f 4 volume ≤ (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
      eLpNorm (fderiv ℝ f) 2 volume := by
  simpa [ScalarEuclideanSobolev.constant] using
    (eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure V) hf hc
      (p := 2) (p' := 4) (by norm_num) (by simp) (by norm_num))

private theorem h2_norm_sum_estimate (g : V → (V →L[ℝ] ℂ))
    (f : V → ℂ) (D : Fin 4 → V → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume)
    (hD : ∀ i, AEStronglyMeasurable (D i) volume)
    (hb : ∀ x, ‖g x‖ ≤ B * ‖f x‖ + ∑ i, ‖D i x‖) :
    eLpNorm g 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume +
      ∑ i : Fin 4, eLpNorm (D i) 2 volume := by
  calc
    _ ≤ eLpNorm (fun x => B * ‖f x‖ + ∑ i : Fin 4, ‖D i x‖) 2 volume :=
      eLpNorm_mono_real hg hb
    _ ≤ eLpNorm (fun x => B * ‖f x‖) 2 volume +
        eLpNorm (fun x => ∑ i : Fin 4, ‖D i x‖) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ ≤ _ := by
      apply add_le_add
      · have he : (fun x => B * ‖f x‖) = B • (fun x => ‖f x‖) := rfl
        rw [he, eLpNorm_const_smul, eLpNorm_norm _ hf]
        simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hB, le_refl]
      · calc
          _ ≤ ∑ i : Fin 4, eLpNorm (fun x => ‖D i x‖) 2 volume := by
            have he : (fun x => ∑ i : Fin 4, ‖D i x‖) =
                ∑ i : Fin 4, (fun x => ‖D i x‖) := by
              funext x
              simp only [Finset.sum_apply]
            rw [he]
            exact eLpNorm_sum_le (μ := (volume : Measure V)) (p := 2)
              (f := fun i : Fin 4 => fun x => ‖D i x‖)
              (s := Finset.univ) (by norm_num)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            exact eLpNorm_norm _ (hD i)

private theorem h2_cutoff_L2_derivative (f : 𝓢(V, ℂ)) (n : ℕ) :
    eLpNorm (fderiv ℝ (fun x => h2Cutoff n x • f x)) 2 volume ≤
      ENNReal.ofReal h2BumpDerivativeBound * eLpNorm f 2 volume +
        ∑ i : Fin 4, eLpNorm
          ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f : 𝓢(V, ℂ)) : V → ℂ) 2 volume := by
  have hg : ContDiff ℝ 1 (fun x => h2Cutoff n x • f x) :=
    ((h2Cutoff_smooth n).of_le (by simp)).smul (f.smooth 1)
  exact h2_norm_sum_estimate _ f _ _ h2BumpDerivativeBound_nonneg
    (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable
    f.continuous.aestronglyMeasurable
    (fun i => (SchwartzMap.continuous _).aestronglyMeasurable)
    (h2_cutoff_fderiv_bound f n)

private theorem h2_cutoff_L4_bound (f : 𝓢(V, ℂ)) (n : ℕ) :
    eLpNorm (fun x => h2Cutoff n x • f x) 4 volume ≤
      (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
        (ENNReal.ofReal h2BumpDerivativeBound * eLpNorm f 2 volume +
          ∑ i : Fin 4, eLpNorm ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f : 𝓢(V, ℂ)) : V → ℂ) 2 volume) := by
  have hg : ContDiff ℝ 1 (fun x => h2Cutoff n x • f x) :=
    ((h2Cutoff_smooth n).of_le (by simp)).smul (f.smooth 1)
  exact (h2_compact_critical _ hg (h2Cutoff_compact n).smul_right).trans
    (mul_le_mul_of_nonneg_left (h2_cutoff_L2_derivative f n) (by positivity))

/-- A fixed inhomogeneous critical estimate for Schwartz functions. -/
theorem scalar_schwartz_L4_bound (f : 𝓢(V, ℂ)) :
    eLpNorm f 4 volume ≤
      (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
        (ENNReal.ofReal h2BumpDerivativeBound * eLpNorm f 2 volume +
          ∑ i : Fin 4, eLpNorm ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f : 𝓢(V, ℂ)) : V → ℂ) 2 volume) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (f := fun n x => h2Cutoff n x • f x)
    (Filter.Eventually.of_forall (h2_cutoff_L4_bound f))
    (fun n => ((h2Cutoff_smooth n).continuous.smul f.continuous).aestronglyMeasurable)
    f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      simpa only [one_smul] using (h2Cutoff_tendsto x).smul_const (f x)))

private theorem h2_schwartz_eLpNorm (f : 𝓢(V, ℂ)) :
    eLpNorm f 2 volume = ENNReal.ofReal ‖f.toLp 2 volume‖ := by
  rw [ofReal_norm]
  exact (Lp.enorm_toLp (f.memLp 2 volume)).symm

private theorem h2_L2_injective :
    Function.Injective (fun f : L2 => (f : 𝓢'(V, ℂ))) :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))

private def h2SchwartzInverse (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ
    (fun x : V => (Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)))) f

private theorem h2SchwartzInverse_L2 (f : 𝓢(V, ℂ)) :
    (h2SchwartzInverse f).toLp 2 volume = scalarBesselInverseL2 (f.toLp 2 volume) := by
  apply h2_L2_injective
  change ((h2SchwartzInverse f).toLp 2 volume : 𝓢'(V, ℂ)) =
    (scalarBesselInverseL2 (f.toLp 2 volume) : 𝓢'(V, ℂ))
  rw [scalarBesselInverseL2_distribution, Lp.toTemperedDistribution_toLp_eq,
    Lp.toTemperedDistribution_toLp_eq]
  unfold besselPotential
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (g := fun x : V => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)))
    (by fun_prop) f).symm

private theorem h2SchwartzInverse_first (f : 𝓢(V, ℂ)) (i : Fin 4) :
    (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (h2SchwartzInverse f)).toLp 2 volume =
      scalarBesselFirstL2 i (f.toLp 2 volume) := by
  apply h2_L2_injective
  dsimp only
  rw [scalarBesselFirstL2_distribution, ← h2SchwartzInverse_L2,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact (lineDerivOp_toTemperedDistributionCLM_eq _ _).symm

private theorem h2SchwartzInverse_second (f : 𝓢(V, ℂ)) (i j : Fin 4) :
    (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
      (∂_{EuclideanSpace.basisFun (Fin 4) ℝ j} (h2SchwartzInverse f))).toLp 2 volume =
      scalarBesselSecondL2 i j (f.toLp 2 volume) := by
  apply h2_L2_injective
  dsimp only
  rw [scalarBesselSecondL2_distribution, ← h2SchwartzInverse_L2,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  simp only [scalarCoordinateDerivative]
  rw [lineDerivOp_toTemperedDistributionCLM_eq, lineDerivOp_toTemperedDistributionCLM_eq]

/-- Every first derivative of an H2 distribution has an actual L4 representative. -/
theorem scalar_H2_first_L4 (u : 𝓢'(V, ℂ)) (hu : MemSobolev 2 2 u) (i : Fin 4) :
    ∃ g : L2, (g : 𝓢'(V, ℂ)) = scalarCoordinateDerivative i u ∧
      MemLp (g : V → ℂ) 4 volume := by
  obtain ⟨v, hv⟩ := hu
  have hu' : u = (scalarBesselInverseL2 v : 𝓢'(V, ℂ)) := by
    rw [scalarBesselInverseL2_distribution, ← hv,
      besselPotential_besselPotential_apply]
    norm_num
  refine ⟨scalarBesselFirstL2 i v, ?_, ?_⟩
  · rw [hu', scalarBesselFirstL2_distribution]
  have hdense := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ)
    (μ := (volume : Measure V)) (p := 2) (by norm_num)
  obtain ⟨vs, hvs, ht⟩ := mem_closure_iff_seq_limit.mp (hdense v)
  choose fs hfs using hvs
  have ht' : Tendsto (fun n => (fs n).toLp 2 volume) atTop (𝓝 v) := by
    have he : (fun n => (fs n).toLp 2 volume) = vs := funext (fun n => hfs n)
    rw [he]
    exact ht
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ ht').exists_norm_le
  have hB' (n : ℕ) : ‖(fs n).toLp 2 volume‖ ≤ B := hB _ (mem_range_self n)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  let K : ℝ≥0∞ := (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
    (ENNReal.ofReal h2BumpDerivativeBound * ENNReal.ofReal ((2 * Real.pi) * B) +
      4 * ENNReal.ofReal ((2 * Real.pi) ^ 2 * B))
  have hbound (n : ℕ) : eLpNorm
      (fun x => (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (h2SchwartzInverse (fs n))) x)
      4 volume ≤ K := by
    apply (scalar_schwartz_L4_bound _).trans
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [h2_schwartz_eLpNorm, h2SchwartzInverse_first]
      exact ENNReal.ofReal_le_ofReal ((scalarBesselFirstL2_norm i _).trans
        (mul_le_mul_of_nonneg_left (hB' n) (by positivity)))
    · calc
        _ ≤ ∑ _j : Fin 4, ENNReal.ofReal ((2 * Real.pi) ^ 2 * B) := by
          apply Finset.sum_le_sum
          intro j _
          rw [h2_schwartz_eLpNorm, h2SchwartzInverse_second]
          exact ENNReal.ofReal_le_ofReal ((scalarBesselSecondL2_norm j i _).trans
            (mul_le_mul_of_nonneg_left (hB' n) (by positivity)))
        _ = _ := by simp
  have hconv := (scalarBesselFirstL2 i).continuous.continuousAt.tendsto.comp ht'
  have hconv' := tendstoInMeasure_of_tendsto_Lp hconv
  have hfn (n : ℕ) :
      (scalarBesselFirstL2 i ((fs n).toLp 2 volume) : V → ℂ) =ᵐ[volume]
        (fun x => (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (h2SchwartzInverse (fs n))) x) := by
    rw [← h2SchwartzInverse_first]
    exact SchwartzMap.coeFn_toLp _ _ _
  have hLpbound : ∀ᶠ n in atTop, eLpNorm
      (scalarBesselFirstL2 i ((fs n).toLp 2 volume) : V → ℂ) 4 volume ≤ K :=
    Eventually.of_forall (fun n => by rw [eLpNorm_congr_ae (hfn n)]; exact hbound n)
  exact (eLpNorm_le_of_tendstoInMeasure hLpbound hconv'
      (fun n => (Lp.memLp _).aestronglyMeasurable)).trans_lt (by
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
        ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top⟩))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong L4 continuity of the first derivative of the Bessel inverse.
The existing H2 gradient estimate gives membership; the closed graph theorem
upgrades this to the strong convergence needed in nonlinear second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "L4" => Lp ℂ 4 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem scalarBesselFirstL2_memLp_four (i : Fin 4) (f : L2) :
    MemLp (scalarBesselFirstL2 i f : V → ℂ) 4 volume := by
  obtain ⟨v, hv, h4⟩ := scalar_H2_first_L4 (scalarBesselInverseL2 f : T)
    (scalarBesselInverseL2_memSobolev f) i
  have heq : v = scalarBesselFirstL2 i f := scalarL2_distribution_injective
    (hv.trans (scalarBesselFirstL2_distribution i f).symm)
  simpa only [heq] using h4

private def besselFirstL4Linear (i : Fin 4) : L2 →ₗ[ℂ] L4 where
  toFun f := (scalarBesselFirstL2_memLp_four i f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(scalarBesselFirstL2_memLp_four i (f + g)).coeFn_toLp,
      (scalarBesselFirstL2_memLp_four i f).coeFn_toLp,
      (scalarBesselFirstL2_memLp_four i g).coeFn_toLp,
      Lp.coeFn_add (scalarBesselFirstL2 i f) (scalarBesselFirstL2 i g),
      Lp.coeFn_add ((scalarBesselFirstL2_memLp_four i f).toLp _)
        ((scalarBesselFirstL2_memLp_four i g).toLp _)] with x hfg hf hg h2 h4
    rw [hfg, h4, Pi.add_apply, hf, hg, map_add]
    exact h2
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(scalarBesselFirstL2_memLp_four i (c • f)).coeFn_toLp,
      (scalarBesselFirstL2_memLp_four i f).coeFn_toLp,
      Lp.coeFn_smul c (scalarBesselFirstL2 i f),
      Lp.coeFn_smul c ((scalarBesselFirstL2_memLp_four i f).toLp _)] with x hcf hf h2 h4
    rw [hcf, h4, Pi.smul_apply, hf, map_smul]
    exact h2

private theorem besselFirstL4Linear_coe (i : Fin 4) (f : L2) :
    (besselFirstL4Linear i f : V → ℂ) =ᵐ[volume] scalarBesselFirstL2 i f :=
  (scalarBesselFirstL2_memLp_four i f).coeFn_toLp

/-- The first derivative of the inverse Bessel operator is a continuous map
from L2 to L4 in dimension four. -/
def scalarBesselFirstL4 (i : Fin 4) : L2 →L[ℂ] L4 where
  toLinearMap := besselFirstL4Linear i
  cont := (besselFirstL4Linear i).continuous_of_seq_closed_graph (by
    intro f x y hfx hfy
    have hlow := tendstoInMeasure_of_tendsto_Lp
      ((scalarBesselFirstL2 i).continuous.continuousAt.tendsto.comp hfx)
    have hhigh := tendstoInMeasure_of_tendsto_Lp hfy
    have hlow' : TendstoInMeasure volume
        (fun n => (besselFirstL4Linear i (f n) : V → ℂ)) atTop
        (scalarBesselFirstL2 i x : V → ℂ) :=
      hlow.congr (fun n => (besselFirstL4Linear_coe i (f n)).symm) Filter.EventuallyEq.rfl
    apply Lp.ext
    exact (tendstoInMeasure_ae_unique hhigh hlow').trans
      (besselFirstL4Linear_coe i x).symm)

theorem scalarBesselFirstL4_coe (i : Fin 4) (f : L2) :
    (scalarBesselFirstL4 i f : V → ℂ) =ᵐ[volume] scalarBesselFirstL2 i f :=
  besselFirstL4Linear_coe i f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport between the measurable structure on FourSpace and its equal
Borel structure, preserving functions and Lebesgue measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ENNReal

noncomputable section

abbrev scalarBorelLp (F : Type*) [NormedAddCommGroup F] (p : ℝ≥0∞) : Type _ := by
  letI : MeasurableSpace FourSpace := borel FourSpace
  letI : BorelSpace FourSpace := ⟨rfl⟩
  letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
  exact ↥(Lp F p (volume : Measure FourSpace))

private def scalarBorelLpEquivAux (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : MeasurableSpace FourSpace)
    (hm : m = borel FourSpace) :
    (letI : MeasurableSpace FourSpace := m
     letI : BorelSpace FourSpace := ⟨hm⟩
     letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
     Lp F p (volume : Measure FourSpace)) ≃ₗᵢ[ℝ] scalarBorelLp F p := by
  subst m
  exact LinearIsometryEquiv.refl ℝ _

private theorem scalarBorelLpEquivAux_coe (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : MeasurableSpace FourSpace)
    (hm : m = borel FourSpace)
    (f : (letI : MeasurableSpace FourSpace := m
          letI : BorelSpace FourSpace := ⟨hm⟩
          letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
          Lp F p (volume : Measure FourSpace))) :
    (scalarBorelLpEquivAux F p m hm f : FourSpace → F) = (f : FourSpace → F) := by
  subst m
  rfl

def scalarBorelLpEquiv (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp F p (volume : Measure FourSpace) ≃ₗᵢ[ℝ] scalarBorelLp F p :=
  scalarBorelLpEquivAux F p inferInstance BorelSpace.measurable_eq

theorem scalarBorelLpEquiv_coe (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp F p (volume : Measure FourSpace)) :
    (scalarBorelLpEquiv F p f : FourSpace → F) = (f : FourSpace → F) :=
  scalarBorelLpEquivAux_coe F p inferInstance BorelSpace.measurable_eq f

private theorem scalarBorelLpEquivAux_ae (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : MeasurableSpace FourSpace)
    (hm : m = borel FourSpace)
    (u : (letI : MeasurableSpace FourSpace := m
          letI : BorelSpace FourSpace := ⟨hm⟩
          letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
          Lp F p (volume : Measure FourSpace))) (f : FourSpace → F)
    (hu : letI : MeasurableSpace FourSpace := m
          letI : BorelSpace FourSpace := ⟨hm⟩
          letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
          (u : FourSpace → F) =ᵐ[volume] f) :
    letI : MeasurableSpace FourSpace := borel FourSpace
    letI : BorelSpace FourSpace := ⟨rfl⟩
    letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
    (scalarBorelLpEquivAux F p m hm u : FourSpace → F) =ᵐ[volume] f := by
  subst m
  exact hu

/-- Almost-everywhere representatives are unchanged by the transport. -/
theorem scalarBorelLpEquiv_ae (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Lp F p (volume : Measure FourSpace))
    (f : FourSpace → F) (hu : (u : FourSpace → F) =ᵐ[volume] f) :
    letI : MeasurableSpace FourSpace := borel FourSpace
    letI : BorelSpace FourSpace := ⟨rfl⟩
    letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
    (scalarBorelLpEquiv F p u : FourSpace → F) =ᵐ[volume] f :=
  scalarBorelLpEquivAux_ae F p inferInstance BorelSpace.measurable_eq u f hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local H¹ derivatives give genuine global weak derivatives after a
compact cutoff. No differentiability of an L² representative is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem scalar_partial_product (f q : FourSpace → ℝ) (z : FourSpace)
    (hf : DifferentiableAt ℝ f z) (hq : DifferentiableAt ℝ q z) (i : Fin 4) :
    partialDeriv (fun w => f w * q w) i z =
      partialDeriv f i z * q z + f z * partialDeriv q i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hq, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

def scalarLocalL2PartialProduct {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) (i : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  scalarLocalL2Product hK (fun w => partialDeriv χ i w)
    (((hχ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))).continuous)
    (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) f

theorem scalarLocalL2PartialProduct_integral {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) (i : Fin 4)
    (ψ : FourSpace → ℝ) :
    (∫ z, scalarLocalL2PartialProduct hK χ hχ hc hs f i z * ψ z) =
      ∫ z in K, partialDeriv χ i z * f z * ψ z :=
  scalarLocalL2Product_integral ..

theorem scalarLocalL2_weak_product {K : Set FourSpace} (hK : MeasurableSet K)
    (f g : Lp ℝ 2 (volume.restrict K)) (i : Fin 4)
    (hw : ∀ (q : FourSpace → ℝ), ContDiff ℝ ∞ q → HasCompactSupport q →
      tsupport q ⊆ K → (∫ z in K, f z * partialDeriv q i z) =
        -(∫ z in K, g z * q z))
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    (∫ z, scalarLocalL2Product hK χ hχ.continuous hc hs f z * partialDeriv ψ i z) =
      -((∫ z, scalarLocalL2Product hK χ hχ.continuous hc hs g z * ψ z) +
        ∫ z, scalarLocalL2PartialProduct hK χ hχ hc hs f i z * ψ z) := by
  have hDχ : ContDiff ℝ ∞ (fun w => partialDeriv χ i w) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))
  have hDψ : ContDiff ℝ ∞ (fun w => partialDeriv ψ i w) :=
    (hψ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))
  have hint₁ := scalarLocalL2_mul_integrable f
    (fun z => partialDeriv χ i z * ψ z) (hDχ.continuous.mul hψ.continuous)
    ((hc.fderiv_apply ℝ (coordinateVector i)).mul_right)
  have hint₂ := scalarLocalL2_mul_integrable f
    (fun z => χ z * partialDeriv ψ i z) (hχ.continuous.mul hDψ.continuous) hc.mul_right
  have hweak := hw (fun z => χ z * ψ z) (hχ.mul hψ) hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  have hexpand : (∫ z in K, f z * partialDeriv (fun w => χ w * ψ w) i z) =
      (∫ z in K, f z * (partialDeriv χ i z * ψ z)) +
        ∫ z in K, f z * (χ z * partialDeriv ψ i z) := by
    rw [← integral_add hint₁ hint₂]
    apply integral_congr_ae
    filter_upwards with z
    rw [scalar_partial_product χ ψ z (hχ.differentiable (by simp) z)
      (hψ.differentiable (by simp) z)]
    ring
  rw [hexpand] at hweak
  simp only [scalarLocalL2Product_integral, scalarLocalL2PartialProduct_integral]
  have he₁ : (∫ z in K, f z * (χ z * partialDeriv ψ i z)) =
      ∫ z in K, χ z * f z * partialDeriv ψ i z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  have he₂ : (∫ z in K, f z * (partialDeriv χ i z * ψ z)) =
      ∫ z in K, partialDeriv χ i z * f z * ψ z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  have he₃ : (∫ z in K, g z * (χ z * ψ z)) =
      ∫ z in K, χ z * g z * ψ z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  rw [he₁, he₂, he₃] at hweak
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance localWeak_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1Chart_weak_derivative_integral (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (u : scalarH1 d)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ K) (i : Fin 4) :
    (∫ z in K, scalarH1ChartValue g o d c hK hKt u z * partialDeriv ψ i z) =
      -(∫ z in K, scalarH1ChartDerivative g o d c hK hKt i u z * ψ z) := by
  have hw := scalarH1Chart_weak_derivative g o d c hK hKt u ψ hψ hc hs i
  simp only [L2.inner_def, RCLike.inner_apply', conj_trivial] at hw
  have hD : scalarCompactDerivativeL2 K ψ hψ hc i =ᵐ[volume.restrict K]
      (fun z => partialDeriv ψ i z) := scalarCompactTestL2_coe ..
  have ht := scalarCompactTestL2_coe K ψ hψ.continuous hc
  have he₁ := integral_congr_ae ((Filter.EventuallyEq.rfl
    (f := fun z => scalarH1ChartValue g o d c hK hKt u z)).mul hD)
  have he₂ := integral_congr_ae ((Filter.EventuallyEq.rfl
    (f := fun z => scalarH1ChartDerivative g o d c hK hKt i u z)).mul ht)
  simp only [Pi.mul_apply] at he₁ he₂
  rwa [he₁, he₂] at hw

end
end PositiveEinsteinFour.Geometry
end

end OAI
