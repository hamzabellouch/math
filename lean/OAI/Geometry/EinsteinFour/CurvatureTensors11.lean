import OAI.Geometry.EinsteinFour.FlatDirichletThreshold
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry11
import OAI.Geometry.EinsteinFour.HodgeTheory08
import OAI.Geometry.EinsteinFour.JacobiCurvatureCap
import OAI.Geometry.EinsteinFour.JacobiFiniteLower
import OAI.Geometry.EinsteinFour.JacobiFullCurvatureNorm

namespace OAI


section

/-! Exact second moment of the actual full normal-curvature matrix. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace

omit [PreconnectedSpace M] in
theorem actualJacobiCurvature_frame_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) : Continuous (fun e => actualJacobiCurvature g e t) := by
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp := actualParallelMetricData_reflection g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  have hC : Continuous (frameCurvatureField g) := d.continuousCurvatureField op hRic
  exact continuous_const.add (hC.comp (parallelFrameFlowMap_continuous_slice g 0 t))

omit [PreconnectedSpace M] in
theorem actual_frameCurvature_mean_square (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂canonicalFrameMeasure g o) =
      (3 / 2) * (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp := actualParallelMetricData_reflection g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  have hC : Continuous (frameCurvatureField g) := d.continuousCurvatureField op hRic
  have hi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2)
      (canonicalFrameMeasure g o) :=
    (hC.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (canonicalFrameMeasure_energy g o).curvature_energy Angular.actual_follandMoments
    hRic (actual_orientedNormRegularity o).toPetersenInput (actual_finitePositiveVolume g) hi

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M] in
private theorem full_curvature_norm_square (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ‖1 + frameCurvatureField g e‖ ^ 2 = 3 + ‖frameCurvatureField g e‖ ^ 2 := by
  apply frobenius_sq_one_add_of_trace_zero
  have ht : (frameCurvatureField g e).trace = 0 := by
    have h := frameCurvatureField_add_one_trace g e (actual_einstein_decomposition _ hRic)
      (actual_weyl_traceFree _ hRic).1 (actual_weyl_traceFree _ hRic).2
    rw [Matrix.trace_add, Matrix.trace_one] at h
    norm_num at h
    linarith
  exact ht

omit [PreconnectedSpace M] in
private theorem full_curvature_mean_square (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    (∫ e, ‖1 + frameCurvatureField g e‖ ^ 2 ∂canonicalFrameMeasure g o) =
      3 + (3 / 2) * (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp := actualParallelMetricData_reflection g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  have hC : Continuous (frameCurvatureField g) := d.continuousCurvatureField op hRic
  have hi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2)
      (canonicalFrameMeasure g o) :=
    (hC.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ e, (3 + ‖frameCurvatureField g e‖ ^ 2) ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (full_curvature_norm_square g hRic)
    _ = _ := by
      rw [integral_add (integrable_const _) hi, actual_frameCurvature_mean_square g o hRic]
      simp

omit [PreconnectedSpace M] in
theorem actualJacobiCurvature_mean_square (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) :
    (∫ e, ‖actualJacobiCurvature g e t‖ ^ 2 ∂canonicalFrameMeasure g o) =
      3 + (3 / 2) * (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) := by
  change (∫ e, (fun f : FrameBundle g => ‖1 + frameCurvatureField g f‖ ^ 2)
    (parallelFrameFlowMap g 0 t e) ∂canonicalFrameMeasure g o) = _
  have h := (parallelFrameFlowMap_measurePreserving g o 0 t).integral_comp
    (parallelFrameHomeomorph g 0 t).measurableEmbedding
    (fun e => ‖1 + frameCurvatureField g e‖ ^ 2)
  exact h.trans (full_curvature_mean_square g o hRic)

omit [PreconnectedSpace M] in
theorem actualJacobiCurvature_mean_square_of_energy_three
    (g : SmoothMetric M) (o : FrameOrientation g) (hRic : RicciThree g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    (t : ℝ) :
    (∫ e, ‖actualJacobiCurvature g e t‖ ^ 2 ∂canonicalFrameMeasure g o) = 15 / 2 := by
  rw [actualJacobiCurvature_mean_square g o hRic t, hE]
  norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! The balanced moment argument from the actual index integrals. The same
positive measure factor occurs in the volume bound and both index formulas,
so its numerical value is not needed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {orientation : FrameOrientation g}

theorem MetricGreenData.canonical_balanced_moments
    (d : MetricGreenData g (canonicalFrameMeasure g orientation))
    (op : OppositeWeylData d) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hpinch : ∀ e, d.plusNormField e + d.minusNormField op e < 2)
    (hp : ∃ e ∈ orientation.positive, d.plusNormField e ≠ 0)
    (hm : ∃ e ∈ orientation.positive, d.minusNormField op e ≠ 0)
    (hvp : (∫ e, MomentObstruction.H (d.plusNormField e) ^ 2
          ∂canonicalFrameMeasure g orientation) -
        (∫ e, MomentObstruction.H (d.plusNormField e)
          ∂canonicalFrameMeasure g orientation) ^ 2 ≤
      (9 / 16 : ℝ) * ((∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) -
        ∫ e, d.plusNormField e ∂canonicalFrameMeasure g orientation))
    (hvm : (∫ e, MomentObstruction.H (d.minusNormField op e) ^ 2
          ∂canonicalFrameMeasure g orientation) -
        (∫ e, MomentObstruction.H (d.minusNormField op e)
          ∂canonicalFrameMeasure g orientation) ^ 2 ≤
      (9 / 16 : ℝ) * ((∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation) -
        ∫ e, d.minusNormField op e ∂canonicalFrameMeasure g orientation)) :
    (∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) =
      ∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hi {f : FrameBundle g → ℝ} (hf : Continuous f) :
      Integrable f (canonicalFrameMeasure g orientation) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn := (actual_orientedNormRegularity orientation).toPetersenInput
  have hvol := actual_finitePositiveVolume g
  have hib := orientedNormSquares_integrable orientation hn hvol
  have hframe := norm_square_frame_integrals
    (canonicalFrameMeasure_energy g orientation).averaging Angular.actual_follandMoments hn
    (canonicalFrameMeasure_supported g orientation)
    (hi (d.plusNormField.continuous.pow 2))
    (hi ((d.minusNormField op).continuous.pow 2)) hib.1 hib.2
  change ((∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) = _) ∧
    ((∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation) = _) at hframe
  have hupper := normalized_volume_ratio_upper g orientation hRic hpositive
  rw [integral_add hib.1 hib.2, ← hframe.1, ← hframe.2] at hupper
  obtain ⟨n, m, heuler, hsignature⟩ := normalized_hodge_counts g orientation hRic
  rw [← hframe.1, ← hframe.2] at heuler hsignature
  have hgap := actual_gurskyLeBrunGap g orientation hRic
  have hplusgap : 1 ≤ ∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation := by
    obtain ⟨e, he, hne⟩ := hp
    have he' : plusNorm orientation e.base ≠ 0 := by
      rw [hn.plusFrame e he]
      exact hne
    rw [hframe.1]
    exact hgap.1 ⟨e.base, he'⟩
  have hminusgap : 1 ≤ ∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation := by
    obtain ⟨e, he, hne⟩ := hm
    have he' : minusNorm orientation e.base ≠ 0 := by
      rw [hn.minusFrame e he]
      exact hne
    rw [hframe.2]
    exact hgap.2 ⟨e.base, he'⟩
  have hpb (e : FrameBundle g) : d.plusNormField e ∈ Set.Icc (0 : ℝ) 2 := by
    refine ⟨normalizedBlockNorm_nonneg _, ?_⟩
    have hb : 0 ≤ d.minusNormField op e := normalizedBlockNorm_nonneg _
    linarith only [hpinch e, hb]
  have hmb (e : FrameBundle g) : d.minusNormField op e ∈ Set.Icc (0 : ℝ) 2 := by
    refine ⟨normalizedBlockNorm_nonneg _, ?_⟩
    have hv : 0 ≤ d.plusNormField e := normalizedBlockNorm_nonneg _
    linarith only [hpinch e, hv]
  have hHplus : Continuous (fun e => MomentObstruction.H (d.plusNormField e) ^ 2) := by
    unfold MomentObstruction.H
    fun_prop
  have hHminus : Continuous (fun e => MomentObstruction.H (d.minusNormField op e) ^ 2) := by
    unfold MomentObstruction.H
    fun_prop
  exact (balanced_moments n m (2 * (volumeRatio g / riemannianChartFactor.toReal))
    d.plusNormField.continuous.aestronglyMeasurable
    (d.minusNormField op).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hpb) (Filter.Eventually.of_forall hmb)
    (Filter.Eventually.of_forall fun e => (hpinch e).le)
    (hi d.plusNormField.continuous) (hi (d.minusNormField op).continuous)
    (hi (d.plusNormField.continuous.pow 2)) (hi ((d.minusNormField op).continuous.pow 2))
    (hi hHplus) (hi hHminus) hplusgap hminusgap
    (frame_norm_moment_sum_lt_four d op hpinch)
    (mul_pos (by norm_num) (div_pos (volumeRatio_pos hvol) riemannianChartFactor_toReal_pos))
    (by linarith only [hupper]) heuler (by nlinarith only [hsignature]) hvp hvm).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The lower finite determinant estimate for the actual geodesic curvature,
with no spectral or discrete positivity hypothesis. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actual_finite_jacobi_determinant_lower (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    (t : ℝ) (ht : 0 ≤ t) (htop : t < Real.pi / Real.sqrt 3) :
    ∀ᶠ N : ℕ in atTop, ∀ τ : Fin N → ℝ,
      Real.exp ((5 / 6 : ℝ) * Real.log (1 - (3 : ℝ) • scaledFlatGreen t N).det -
        (scaledFlatGreen t N).trace / 2) ≤
      ∫ e, (1 - curvatureKernel (scaledFlatGreen t N)
        (fun i => actualJacobiCurvature g e (τ i))).det ∂canonicalFrameMeasure g o := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  filter_upwards [scaledFlatGreen_eventually_below_one ht htop] with N hN
  intro τ
  let R := fun i e => actualJacobiCurvature g e (τ i)
  have hR : ∀ i, Continuous (R i) := fun i =>
    actualJacobiCurvature_frame_continuous g o hRic (τ i)
  have hp : ∀ i e, (R i e).PosSemidef ∧ (R i e).trace = 3 := by
    intro i e
    exact ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e (τ i)⟩
  exact finite_determinant_lower (flatGreenRoot t N) (scaledFlatGreen t N)
    (flatGreenRoot_square t N) (flatGreenRoot_transpose t N)
    (scaledFlatGreen_posSemidef t N) (scaledFlatGreen_nonneg t N) R hR hp
    (fun i => actualJacobiCurvature_mean_square_of_energy_three g o hRic hE (τ i)) hN
    (fun e => symmetricCurvatureKernel_one_sub_posDef _ _ (flatGreenRoot_square t N)
      (flatGreenRoot_transpose t N) hN _ (fun i => hp i e))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual oriented metric has one vanishing Weyl block. Euler and
signature enter through the proved heat-index integrals, not a published
Hodge assumption. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem actual_one_weyl_block_zero (g : SmoothMetric M) (orientation : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) :
    (∀ c, plusWeyl g c (orientation.frame c) = 0) ∨
      ∀ c, minusWeyl g c (orientation.frame c) = 0 := by
  let p := canonicalParallelMetricData g orientation hRic
  let d := p.toMetricGreenData
  have hparallel : ParallelReflection d := actualParallelMetricData_reflection g
    (canonicalFrameMeasure g orientation)
    (parallelFrameFlowMap_measurePreserving g orientation) hRic
  let op := d.oppositeData hparallel hRic
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hn := (actual_orientedNormRegularity orientation).toPetersenInput
  have hp := shiftedCurvaturePositive_of_published (actual_sectionalInput g) hRic hpositive
  have hpinch := strict_norm_pinching_of_published d op (actual_sectionalInput g) hRic hpositive
  have hdecomp (e : FrameBundle g) : frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) :=
    actual_einstein_decomposition e.frame hRic
  let s : ScalarVarianceInputs d orientation := {
    norms := hn
    orientationFlow := canonicalParallelMetricData_orientation orientation hRic
    supported := canonicalFrameMeasure_supported g orientation
    calculus := p.scalarCalculus.toPetersenInput
    poisson := actual_petersen_poisson g orientation hRic
    positive := hp
    decomposition := hdecomp }
  have hi {f : FrameBundle g → ℝ} (hf : Continuous f) :
      Integrable f (canonicalFrameMeasure g orientation) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hib := orientedNormSquares_integrable orientation hn (actual_finitePositiveVolume g)
  have hframe := norm_square_frame_integrals
    (canonicalFrameMeasure_energy g orientation).averaging Angular.actual_follandMoments hn
    (canonicalFrameMeasure_supported g orientation)
    (hi (d.plusNormField.continuous.pow 2))
    (hi ((d.minusNormField op).continuous.pow 2)) hib.1 hib.2
  change ((∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) = _) ∧
    ((∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation) = _) at hframe
  have hgap := actual_gurskyLeBrunGap g orientation hRic
  have hpgap : (∃ e ∈ orientation.positive, d.plusNormField e ≠ 0) →
      1 ≤ ∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation := by
    rintro ⟨e, he, hne⟩
    have he' : plusNorm orientation e.base ≠ 0 := by
      rw [hn.plusFrame e he]
      exact hne
    rw [hframe.1]
    exact hgap.1 ⟨e.base, he'⟩
  have hmgap : (∃ e ∈ orientation.positive, d.minusNormField op e ≠ 0) →
      1 ≤ ∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation := by
    rintro ⟨e, he, hne⟩
    have he' : minusNorm orientation e.base ≠ 0 := by
      rw [hn.minusFrame e he]
      exact hne
    rw [hframe.2]
    exact hgap.2 ⟨e.base, he'⟩
  have hz : (∀ e ∈ orientation.positive, d.plusNormField e = 0) ∨
      ∀ e ∈ orientation.positive, d.minusNormField op e = 0 := by
    classical
    by_cases hv : ∀ e ∈ orientation.positive, d.plusNormField e = 0
    · exact Or.inl hv
    by_cases hb : ∀ e ∈ orientation.positive, d.minusNormField op e = 0
    · exact Or.inr hb
    push Not at hv hb
    have hsecond := d.canonical_balanced_moments op hRic hpositive hpinch hv hb
      (d.plusHVariance op s hparallel hpinch) (d.minusHVariance op s hparallel hpinch)
    exact d.one_block_zero_of_variance op orientation hparallel hp hdecomp hpinch hsecond
      (d.normDifferenceVariance op s hparallel hpinch)
      (d.plusNormVariance op s hparallel hpinch) (d.minusNormVariance op s hparallel hpinch)
      hpgap hmgap
  rcases hz with hz | hz
  · exact Or.inl (fun c => (plusNorm_eq_zero_iff orientation c).mp (by
      rw [hn.plusFrame ⟨c, orientation.frame c⟩ (orientation.frame_positive c)]
      exact hz ⟨c, orientation.frame c⟩ (orientation.frame_positive c)))
  · exact Or.inr (fun c => (minusNorm_eq_zero_iff orientation c).mp (by
      rw [hn.minusFrame ⟨c, orientation.frame c⟩ (orientation.frame_positive c)]
      exact hz ⟨c, orientation.frame c⟩ (orientation.frame_positive c)))

end
end PositiveEinsteinFour.Geometry
end

end OAI
