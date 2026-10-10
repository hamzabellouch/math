import Mathlib

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal
namespace CKSIntrinsicGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace


theorem chart_inverse_distance_bound (x : M) :
    ∃ (C : ℝ≥0) (r : ℝ), 0 < C ∧ 0 < r ∧
      Metric.ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∧
      ∀ u ∈ Metric.ball (extChartAt I x x) r ∩ range I,
        ∀ v ∈ Metric.ball (extChartAt I x x) r ∩ range I,
          riemannianEDist I ((extChartAt I x).symm u) ((extChartAt I x).symm v) ≤
            C * edist u v := by
  let d (y : E) : E →L[ℝ] TangentSpace I ((extChartAt I x).symm y) :=
    mfderiv[range I] (extChartAt I x).symm y
  obtain ⟨C, hCpos, hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt I x
  obtain ⟨r, hrpos, hr⟩ : ∃ r > 0,
      ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖d y‖ₑ < C} :=
    mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  refine ⟨C, r, hCpos, hrpos, fun y hy => (hr hy).1, ?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := (extChartAt I x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
      {y | ‖d y‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact (((convex_ball _ _).inter I.convex_range).segment_subset hu hv).trans hr
  simp only [preimage_inter, subset_inter_iff] at hη
  have ηsmooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hlen : riemannianEDist I ((extChartAt I x).symm u) ((extChartAt I x).symm v) ≤
      pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp ηsmooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  apply hlen.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hder : mfderiv[Icc 0 1] γ t =
      (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact ηsmooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hvder : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hder 1)
  rw [hvder]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end CKSIntrinsicGeometry

end

end OAI
