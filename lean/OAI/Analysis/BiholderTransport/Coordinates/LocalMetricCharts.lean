import Mathlib

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal NNReal ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]
local notation "𝒥" => 𝓘(ℝ,E)

lemma exists_lipschitzOn_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ball (extChartAt 𝓘(ℝ,E) x x) r ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,E) x).symm
        (ball (extChartAt 𝓘(ℝ,E) x x) r) := by
  let (y : E) : ENorm (TangentSpace 𝒥 y →L[ℝ]
      TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)) :=
    inferInstanceAs (ENorm (E →L[ℝ] TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝒥 x
  obtain ⟨r,hrpos,hr⟩ : ∃ r > 0,
      ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} := by
    have hh := inter_mem (extChartAt_target_mem_nhdsWithin (I := 𝒥) x) hC
    have hh' : (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} ∈
        𝓝 (extChartAt 𝒥 x x) := by
      simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at hh ⊢
      convert hh using 1
      rfl
    exact Metric.mem_nhds_iff.mp hh'
  refine ⟨C,r,hrpos,fun y hy => (hr hy).1,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := (extChartAt 𝒥 x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝒥 x).target ∩
      {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)}) := by
    simp only [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap,η]
    exact ((convex_ball _ _).segment_subset hu hv).trans hr
  simp only [preimage_inter,subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hh : riemannianEDist 𝒥 ((extChartAt 𝒥 x).symm u) ((extChartAt 𝒥 x).symm v) ≤
      pathELength 𝒥 γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := 𝒥)]
  apply hh.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hd : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hd1 : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hd 1)
  rw [hd1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in

lemma hausdorff_nondifferentiable_chart_image_null {u : M → ℝ} {K C : ℝ≥0}
    (hu : LipschitzWith K u) (x : M) {r : ℝ}
    (hr : ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target)
    (hC : LipschitzOnWith C (extChartAt 𝒥 x).symm (ball (extChartAt 𝒥 x x) r)) :
    (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      {y | y ∈ (extChartAt 𝒥 x).symm '' ball (extChartAt 𝒥 x x) r ∧
        ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y} = 0 := by
  let B : Set E := {z | z ∈ ball (extChartAt 𝒥 x x) r ∧
    ¬ DifferentiableAt ℝ (u ∘ (extChartAt 𝒥 x).symm) z}
  have hB : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure E) B = 0 := by
    have hh := (hu.comp_lipschitzOnWith hC).ae_differentiableWithinAt_of_mem
      (μ := (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure E))
    apply measure_mono_null _ (ae_iff.mp hh)
    intro z hz hdiff
    exact hz.2 ((hdiff hz.1).differentiableAt (isOpen_ball.mem_nhds hz.1))
  have himage : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      ((extChartAt 𝒥 x).symm '' B) = 0 := by
    apply le_antisymm ?_ (by positivity)
    have hh := (hC.mono (show B ⊆ ball (extChartAt 𝒥 x x) r from fun _ h => h.1)).hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
    simpa only [hB,mul_zero] using hh
  apply measure_mono_null _ himage
  rintro y ⟨⟨z,hz,rfl⟩,hnot⟩
  refine ⟨z,⟨hz,?_⟩,rfl⟩
  intro hdiff
  apply hnot
  have hsrc : (extChartAt 𝒥 x).symm z ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝒥 x).map_target (hr hz)
  have hD : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (u ∘ (extChartAt 𝒥 x).symm)
      ((extChartAt 𝒥 x) ((extChartAt 𝒥 x).symm z)) := by
    rw [(extChartAt 𝒥 x).right_inv (hr hz)]
    exact hdiff.mdifferentiableAt
  have hh := hD.comp ((extChartAt 𝒥 x).symm z)
    (mdifferentiableAt_extChartAt (I := 𝒥) hsrc)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds hsrc] with w hw
  have hw' : w ∈ (extChartAt 𝒥 x).source := by simpa only [extChartAt_source] using hw
  simp only [Function.comp_apply,(extChartAt 𝒥 x).left_inv hw']

lemma exists_nhds_nondifferentiable_null {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (x : M) :
    ∃ U ∈ 𝓝 x, (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      {y | y ∈ U ∧ ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y} = 0 := by
  obtain ⟨C,r,hrpos,hr,hC⟩ := exists_lipschitzOn_inverse_chart (E := E) x
  let U := (extChartAt 𝒥 x).source ∩
    (extChartAt 𝒥 x) ⁻¹' ball (extChartAt 𝒥 x x) r
  have hU : U ∈ 𝓝 x := by
    apply inter_mem
    · simpa only [extChartAt_source] using chart_source_mem_nhds E x
    · exact (continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ hrpos)
  refine ⟨U,hU,?_⟩
  apply measure_mono_null _ (hausdorff_nondifferentiable_chart_image_null hu x hr hC)
  intro y hy
  exact ⟨⟨(extChartAt 𝒥 x) y,hy.1.2,(extChartAt 𝒥 x).left_inv hy.1.1⟩,hy.2⟩

lemma lipschitz_ae_mdifferentiable [CompactSpace M] {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ x ∂(Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M),
      MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u x := by
  classical
  choose U hUnhds hUnull using exists_nhds_nondifferentiable_null (E := E) hu
  obtain ⟨s,_,hs⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hUnhds x)
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ x ∈ (s : Set M),
    {y | y ∈ U x ∧ ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y})
  · intro y hy
    obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy⟩
  · exact (measure_biUnion_null_iff s.countable_toSet).mpr (fun x _ => hUnull x)

end WeakMTWTransport

end

end OAI
