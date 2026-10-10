import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedResidueObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexHeight

namespace OAI

/-! Continuity of the actual translated theta coefficient and its radial kernel. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaShiftedCell_integral_continuous
    {F : {v : ℝ // 0<v} → ℂ → ℂ} (hF : Continuous F.uncurry) :
    Continuous (fun v => ∫ z in cubicThetaShiftedHorizontalCell,F v z) := by
  let : LocallyCompactSpace {v : ℝ // 0<v} := isOpen_Ioi.locallyCompactSpace
  let : IsFiniteMeasure ((volume : Measure ℂ).restrict cubicThetaShiftedHorizontalCell) :=
    isFiniteMeasure_restrict.mpr (by
      obtain ⟨L,hL,hcell⟩ := cubicThetaShiftedHorizontalCell_compact_container
      exact (lt_of_le_of_lt (measure_mono hcell) hL.measure_lt_top).ne)
  apply continuous_iff_continuousAt.mpr
  intro v
  obtain ⟨U,hU,hUv⟩ := exists_compact_mem_nhds v
  obtain ⟨L,hL,hcell⟩ := cubicThetaShiftedHorizontalCell_compact_container
  obtain ⟨M,hM⟩ := (hU.prod hL).bddAbove_image hF.norm.continuousOn
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards with u
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine ⟨M,?_⟩
    filter_upwards [hUv] with u hu
    filter_upwards [ae_restrict_mem cubicThetaShiftedHorizontalCell_measurable] with z hz
    exact hM (mem_image_of_mem _ (show (u,z)∈U ×ˢ L from ⟨hu,hcell hz⟩))
  · filter_upwards with z
    exact (hF.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

def cubicThetaShiftedModelHorizontal (b h : Eisenstein) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaShiftedHorizontalCell,
    star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (z,v))

lemma cubicThetaShiftedModelHorizontal_continuous (b h : Eisenstein) :
    ContinuousOn (cubicThetaShiftedModelHorizontal b h) (Ioi (0:ℝ)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply cubicThetaShiftedCell_integral_continuous
  change Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
    star (Real.fourierChar (tracePair q.2 (cubicThetaShiftedRowFrequency h)):ℂ)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (q.2,q.1.val)))
  have hc := (cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar).comp
    (continuous_const_smul (cubicThetaShiftedInversion b))
  have ht : Continuous (fun p : CubicThetaPoint =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)) := by
    simpa only [Function.comp_def,cubicThetaFullPointAction_apply] using hc
  have hp : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      (⟨(q.2,q.1.val),q.1.property⟩ : CubicThetaPoint)) :=
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  have hchar : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      Real.fourierChar (tracePair q.2 (cubicThetaShiftedRowFrequency h))) :=
    Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
  have he : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      star (Real.fourierChar (tracePair q.2 (cubicThetaShiftedRowFrequency h)):ℂ)) :=
    (continuous_subtype_val.comp hchar).star
  have hm : Continuous (fun q : {v : ℝ // 0<v} × ℂ =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (q.2,q.1.val))) :=
    (ht.comp hp).congr (fun _ => rfl)
  exact he.mul hm

def cubicThetaShiftedPoleRadial (h : Eisenstein) (v : ℝ) : ℂ :=
  (v:ℂ)^(4/3:ℂ)*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v (4/3) (cubicThetaShiftedRowHeatScale h) t)

lemma cubicThetaShiftedPoleRadial_height (h : Eisenstein) {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedPoleRadial h v=
      (v:ℂ)*cubicThetaComplexHeightIntegral (4/3) (cubicThetaShiftedRowHeatScale h) v := by
  unfold cubicThetaShiftedPoleRadial
  rw [cubicThetaHeat_height_dilation hv,cubicThetaComplexHeightIntegral_real]

lemma cubicThetaShiftedPoleRadial_continuous {h : Eisenstein} (hh : h≠0) :
    ContinuousOn (cubicThetaShiftedPoleRadial h) (Ioi (0:ℝ)) := by
  intro v hv
  apply ContinuousWithinAt.congr_of_eventuallyEq
    ((Complex.continuous_ofReal.continuousAt.mul
      (((cubicThetaComplexHeightIntegral_analytic (4/3)
        (cubicThetaShiftedRowHeatScale_pos hh) (z:=(v:ℂ)) (by simpa using hv)).continuousAt).comp
          Complex.continuous_ofReal.continuousAt)).continuousWithinAt) ?_
    (cubicThetaShiftedPoleRadial_height h hv)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (cubicThetaShiftedPoleRadial_height h hu)

end CubicFirstMoment

end

end OAI
