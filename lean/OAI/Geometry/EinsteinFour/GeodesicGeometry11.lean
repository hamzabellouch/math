import OAI.Geometry.EinsteinFour.CurvatureTensors02
import OAI.Geometry.EinsteinFour.FrameVolume
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.HodgeTheory08
import OAI.Geometry.EinsteinFour.HodgeTheory09
import OAI.Geometry.EinsteinFour.HodgeTheory11
import OAI.Geometry.EinsteinFour.ScalarRegularity06

namespace OAI


section

/-! The nonround half-flat branch has an actual nonzero self-dual harmonic
two-form, by the proved signature formula and Weyl gap. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [SecondCountableTopology M] in
theorem halfFlat_positive_signature (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    0 < (deRhamSignature (o := o) hRic : ℝ) := by
  have hm : ∀ x, minusNorm o x = 0 :=
    fun x => (minusNorm_eq_zero_iff o x).mpr (hminus x)
  have hp : ∃ x, plusNorm o x ≠ 0 := by
    obtain ⟨x, hx⟩ := hplus
    exact ⟨x, fun h => hx ((plusNorm_eq_zero_iff o x).mp h)⟩
  have hgap := (actual_gurskyLeBrunGap g o hRic).1 hp
  have hsig := deRhamSignature_curvature_counts (o := o) hRic
  have hmI : (∫ x, minusNorm o x ^ 2 ∂normalizedVolume g) = 0 := by
    simp only [hm, zero_pow (by decide : 2 ≠ 0), integral_zero]
  rw [hmI, sub_zero] at hsig
  have hrhs : 0 < (4 / 3 : ℝ) * volumeRatio g *
      (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) :=
    mul_pos (mul_pos (by norm_num) (volumeRatio_pos (actual_finitePositiveVolume g)))
      (lt_of_lt_of_le zero_lt_one hgap)
  have hprod : 0 < riemannianChartFactor.toReal * (deRhamSignature (o := o) hRic : ℝ) :=
    hsig.symm ▸ hrhs
  exact (mul_pos_iff_of_pos_left riemannianChartFactor_toReal_pos).mp hprod

omit [SecondCountableTopology M] in
theorem halfFlat_positive_harmonic_dimension (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    0 < Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  have h := halfFlat_positive_signature hRic hminus hplus
  rw [deRhamSignature_hodge] at h
  push_cast at h
  have hn : (0 : ℝ) ≤ Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) :=
    Nat.cast_nonneg _
  have hp : (0 : ℝ) < Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by linarith
  exact_mod_cast hp

local instance projectiveHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

local instance projectivePositiveAddGroup (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicPositive (o := o) hRic) := Submodule.addCommGroup _

omit [SecondCountableTopology M] in
theorem halfFlat_exists_positive_harmonic (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    ∃ u : smoothHarmonicPositive (o := o) hRic, u ≠ 0 :=
  (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
    (M := smoothHarmonicPositive (o := o) hRic)).mp
      (halfFlat_positive_harmonic_dimension hRic hminus hplus)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Retain the actual chart-volume factor throughout polar integration.
It is the same positive factor as in the Euler and signature integrals. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

omit [Nonempty M] in
theorem volumeMeasure_le_normalized_sphericalJacobi (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q : Directions,
        actualRadialMass g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure) := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he, polarAngularMass_eq] at h
  refine h.trans ?_
  gcongr
  exact actualJacobi_cutoff_lintegral_le g hRic _ _
    (actualCutTime_le_firstConjugateTime g hRic _)

theorem volumeMeasure_le_normalized_canonicalRadialMass (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) *
        ∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o) := by
  have h := lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono
    (fun e he => volumeMeasure_le_normalized_sphericalJacobi g o hRic e he))
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  simpa only [lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ hk,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    canonicalFrame_lintegral_sphere_rotations g o _ (measurable_actualRadialMass g hRic)] using h

theorem normalized_totalVolume_le_actualJacobiIntegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    totalVolume g / riemannianChartFactor.toReal ≤ (2 * Real.pi ^ 2) *
      ∫ r in (0 : ℝ)..Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o := by
  have h := volumeMeasure_le_normalized_canonicalRadialMass g o hRic
  rw [canonical_actualRadialMass_eq, ← ENNReal.ofReal_mul (by positivity)] at h
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hk ENNReal.ofReal_ne_top) h
  have hn : 0 ≤ (2 * Real.pi ^ 2) *
      ∫ r in Icc (0 : ℝ) Real.pi, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le] at hreal
  exact (div_le_iff₀ riemannianChartFactor_toReal_pos).mpr (by
    simpa only [totalVolume, mul_comm] using hreal)

theorem normalized_actualJacobiPolar (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    volumeRatio g / riemannianChartFactor.toReal ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ e,
          (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
            ∂canonicalFrameMeasure g o) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ e,
          (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
            ∂canonicalFrameMeasure g o) := by
  let F : ℝ → ℝ := fun r => ∫ e,
    (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o
  have hvolume := normalized_totalVolume_le_actualJacobiIntegral g o hRic
  change totalVolume g / riemannianChartFactor.toReal ≤
    (2 * Real.pi ^ 2) * ∫ r in (0 : ℝ)..Real.pi, F r at hvolume
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
  unfold volumeRatio
  rw [div_right_comm]
  apply (div_le_iff₀ (by positivity : 0 < 8 * Real.pi ^ 2 / 3)).mpr
  convert hvolume using 1
  dsimp only [F]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial determinant estimate with the actual volume factor retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

/-- The two time-zero energies and the parallel-frame/Jacobi/polar construction give
the manuscript's upper-volume deficit. -/
theorem normalized_volume_ratio_upper_of_frame_flow
    (g : SmoothMetric M) [CompactSpace (FrameBundle g)]
    {μ : Measure (FrameBundle g)} [IsProbabilityMeasure μ]
    (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun r => frameCurvatureField g (φ.map r e))
      (frameCurvatureDerivative g (φ.map t e)) t)
    {s : ℝ}
    (hCmean : (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) = (3 / 2) * s)
    (hHmean : (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤ (9 / 4) * s)
    (d : (u : ℝ) → FrameBundle g → Jacobi.RegularJacobi (Real.pi * u))
    (hR : ∀ u e r, (d u e).R r = 1 + frameCurvatureField g (φ.map r e))
    (hpos : ∀ u e r, ((d u e).R r).PosSemidef)
    (htrace : ∀ u e r, ((d u e).R r).trace = 3)
    (hD : ∀ u, 0 < u → u < 1 → Integrable (fun e => (d u e).truncatedDensity) μ)
    (hD0 : IntervalIntegrable (fun u => ∫ e, (d u e).truncatedDensity ∂μ)
      volume 0 (5 / 8))
    (hD1 : IntervalIntegrable (fun u => ∫ e, (d u e).truncatedDensity ∂μ)
      volume (5 / 8) 1)
    (hpolar : volumeRatio g / riemannianChartFactor.toReal ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ e, (d u e).truncatedDensity ∂μ) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ e, (d u e).truncatedDensity ∂μ)) :
    volumeRatio g / riemannianChartFactor.toReal ≤ 1 - (3 / 40) * s := by
  have hs : 0 ≤ s := by
    have hnonneg : 0 ≤ ∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    rw [hCmean] at hnonneg
    linarith
  have hLip (u : ℝ) (_hu : 0 < u) (_hu1 : u < 1) (e : FrameBundle g) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
        ‖Averages.sineWeight a • Jacobi.radialCurvature (d u e).R (Real.pi * u) a -
          Averages.sineWeight b • Jacobi.radialCurvature (d u e).R (Real.pi * u) b‖ ≤
            L * |a - b| := by
    obtain ⟨L, hL, hbound⟩ := frameWeighted_lipschitz φ hC hH hpoint (Real.pi * u) e
    refine ⟨L, hL, ?_⟩
    intro a b
    simpa only [Jacobi.radialCurvature, hR, add_sub_cancel_left, mul_comm]
      using hbound a b
  exact Jacobi.volume_ratio_upper_of_jacobi d hs
    (curvatureCurve_hasDerivAt φ hC hH hpoint)
    (curvatureCurve_energy φ hC hCmean)
    (curvatureDerivativeCurve_energy φ hH hHmean)
    hR hpos htrace hLip hD hD0 hD1 hpolar

end

end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature-energy volume deficit in the normalization used
by the proved Euler and signature integrals. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
local instance normalizedGeometricVolumeNorm : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup
local instance normalizedGeometricVolumeSpace : NormedSpace ℝ Mat3 :=
  Matrix.frobeniusNormedSpace

theorem normalized_volume_ratio_upper (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) :
    volumeRatio g / riemannianChartFactor.toReal ≤ 1 - (3 / 40) *
      (∫ c, plusNorm o c ^ 2 + minusNorm o c ^ 2 ∂normalizedVolume g) := by
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp : ParallelReflection d := actualParallelMetricData_reflection g
    (canonicalFrameMeasure g o) (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  let j := (actualJacobiRealizationData g o hRic
    (actualJacobiPolarInput_proved g o hRic)).toParallelJacobiData op hRic
  let w := canonicalFrameMeasure_energy g o
  let : CompactSpace (FrameBundle g) := j.compact
  have hnorm := (actual_orientedNormRegularity o).toPetersenInput
  have hvol := actual_finitePositiveVolume g
  have hCi := (j.curvatureContinuous.norm.pow 2).integrable_of_hasCompactSupport
    (μ := canonicalFrameMeasure g o) (HasCompactSupport.of_compactSpace _)
  have hDi := (j.derivativeContinuous.norm.pow 2).integrable_of_hasCompactSupport
    (μ := canonicalFrameMeasure g o) (HasCompactSupport.of_compactSpace _)
  apply normalized_volume_ratio_upper_of_frame_flow g j.flow j.curvatureContinuous
    j.derivativeContinuous j.derivative
    (w.curvature_energy actual_follandMoments hRic hnorm hvol hCi)
    (w.derivative_energy d op hp actual_follandMoments hRic hpositive hnorm hvol hDi)
    j.jacobi j.curvature
  · intro u e r
    rw [j.curvature]
    exact actual_jacobi_posSemidef hpositive _
  · intro u e r
    rw [j.curvature]
    exact frameCurvatureField_add_one_trace g _ (actual_einstein_decomposition _ hRic)
      (actual_weyl_traceFree _ hRic).1 (actual_weyl_traceFree _ hRic).2
  · exact j.densityIntegrable
  · exact j.firstIntegral
  · exact j.secondIntegral
  · exact normalized_actualJacobiPolar g o hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual harmonic dimensions give both integer identities with the
common chart-volume factor divided out. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

theorem normalized_hodge_counts (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    ∃ n m : ℕ,
      2 + (n : ℝ) + (m : ℝ) = 2 * (volumeRatio g / riemannianChartFactor.toReal) *
        (1 + (∫ c, plusNorm o c ^ 2 ∂normalizedVolume g) +
          ∫ c, minusNorm o c ^ 2 ∂normalizedVolume g) ∧
      (n : ℝ) - (m : ℝ) = (4 / 3 : ℝ) *
        (volumeRatio g / riemannianChartFactor.toReal) *
        ((∫ c, plusNorm o c ^ 2 ∂normalizedVolume g) -
          ∫ c, minusNorm o c ^ 2 ∂normalizedVolume g) := by
  have he := hodgeComplexEuler_curvature_counts hRic (canonicalParallelMetricData g o hRic)
  have hs := deRhamSignature_curvature_counts (o := o) hRic
  rw [hodgeComplexEuler_hodge hRic] at he
  rw [deRhamSignature_hodge hRic] at hs
  push_cast at he hs
  refine ⟨Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic),
    Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic), ?_, ?_⟩
  · field_simp [riemannianChartFactor_toReal_pos.ne']
    nlinarith only [he]
  · field_simp [riemannianChartFactor_toReal_pos.ne']
    nlinarith only [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual harmonic dimension determines the volume and Weyl energy
in the nonzero half-flat branch. Sectional pinching bounds that dimension. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_volume_energy_counts (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    volumeRatio g / riemannianChartFactor.toReal =
        1 - (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) / 4 ∧
      (volumeRatio g / riemannianChartFactor.toReal) *
        (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) =
        3 * (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) / 4 := by
  have he := hodgeComplexEuler_curvature_counts hRic (canonicalParallelMetricData g o hRic)
  have hs := deRhamSignature_curvature_counts (o := o) hRic
  rw [hodgeComplexEuler_hodge hRic, halfFlat_negative_harmonic_dimension_zero hRic hminus] at he
  rw [deRhamSignature_hodge hRic, halfFlat_negative_harmonic_dimension_zero hRic hminus] at hs
  have hm : ∀ x, minusNorm o x = 0 := fun x => (minusNorm_eq_zero_iff o x).mpr (hminus x)
  simp only [hm, zero_pow (by decide : 2 ≠ 0), integral_zero] at he hs
  push_cast at he hs
  constructor
  · apply (div_eq_iff riemannianChartFactor_toReal_pos.ne').mpr
    nlinarith only [he, hs]
  · field_simp [riemannianChartFactor_toReal_pos.ne']
    nlinarith only [hs]

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M] in
theorem actual_oriented_norm_pinching (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (x : M) :
    plusNorm o x + minusNorm o x < 2 := by
  obtain ⟨a,b,ha,hb,hab⟩ := actual_sectionalInput g hRic hpositive ⟨x,o.frame x⟩
  have hp := QuaternionFrame.normalizedBlockNorm_le_shift _
    (actual_weyl_symmetric (o.frame x)).1 (actual_weyl_traceFree (o.frame x) hRic).1 a ha
  have hm := QuaternionFrame.normalizedBlockNorm_le_shift _
    (actual_weyl_symmetric (o.frame x)).2 (actual_weyl_traceFree (o.frame x) hRic).2 b hb
  change normalizedBlockNorm _ + normalizedBlockNorm _ < 2
  linarith only [hp,hm,hab]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem actual_plus_energy_le_four (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) :
    (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) ≤ 4 := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hi := ((continuous_plusNorm g o).pow 2).integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ _ : M, (4 : ℝ) ∂normalizedVolume g := integral_mono hi (integrable_const _) (by
      intro x
      change plusNorm o x ^ 2 ≤ 4
      have hp := actual_oriented_norm_pinching (o := o) hRic hpositive x
      have hn := plusNorm_nonneg o x
      have hm := minusNorm_nonneg o x
      nlinarith)
    _ = 4 := by simp

theorem halfFlat_positive_harmonic_dimension_le_two (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) ≤ 2 := by
  obtain ⟨hv,he⟩ := halfFlat_volume_energy_counts hRic hminus
  have hV : 0 < volumeRatio g / riemannianChartFactor.toReal :=
    div_pos (volumeRatio_pos (actual_finitePositiveVolume g)) riemannianChartFactor_toReal_pos
  have hE := actual_plus_energy_le_four (o := o) hRic hpositive
  have hn : (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) < 3 := by
    nlinarith
  exact Nat.le_of_lt_succ (by exact_mod_cast hn)

theorem halfFlat_positive_harmonic_dimension_cases (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1 ∨
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 2 := by
  have hp := halfFlat_positive_harmonic_dimension hRic hminus hplus
  have hu := halfFlat_positive_harmonic_dimension_le_two hRic hpositive hminus
  omega

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one half-flat branch attains equality in the Weyl gap;
the actual Weyl norm is consequently identically one. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_plusNorm_eq_one_of_energy_one (hRic : RicciThree g)
    (henergy : (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) = 1) :
    ∀ x, plusNorm o x = 1 := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let : Measure.IsOpenPosMeasure (normalizedVolume g) := normalizedVolume_isOpenPosMeasure g
  exact weyl_gap_equality_constant (normalizedVolume g)
    ⟨plusNorm o, continuous_plusNorm g o⟩ (plusNorm_nonneg o) henergy
    (actual_weyl_gap_limiting_inequality hRic)

variable [SecondCountableTopology M]

theorem halfFlat_dimension_one_energy (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) = 1 := by
  obtain ⟨hv,he⟩ := halfFlat_volume_energy_counts hRic hminus
  rw [hdim] at hv he
  norm_num at hv he
  rw [hv] at he
  linarith

theorem halfFlat_dimension_one_norm (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ∀ x, plusNorm o x = 1 :=
  actual_plusNorm_eq_one_of_energy_one hRic (halfFlat_dimension_one_energy hRic hminus hdim)

end
end PositiveEinsteinFour.Geometry
end

end OAI
