import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma inverse_chart_intrinsic_lipschitz (p : M) :
    ∃ r > (0 : ℝ), ∃ C : ℝ≥0, 0 < C ∧
      ball (extChartAt 𝓘(ℝ,E) p p) r ⊆ (extChartAt 𝓘(ℝ,E) p).target ∧
      ∀ y ∈ ball (extChartAt 𝓘(ℝ,E) p p) r, ∀ z ∈ ball (extChartAt 𝓘(ℝ,E) p p) r,
        riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm y) ((extChartAt 𝓘(ℝ,E) p).symm z)
          ≤ C * edist y z := by
  let c := extChartAt 𝓘(ℝ,E) p
  let d (y : E) : E →L[ℝ] TangentSpace 𝓘(ℝ,E) (c.symm y) :=
    mfderiv[Set.range 𝓘(ℝ,E)] c.symm y
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝓘(ℝ,E) p
  obtain ⟨r,hr,hrsub'⟩ : ∃ r > 0, ball (c p) r ∩ range 𝓘(ℝ,E) ⊆
      c.target ∩ {y | ‖d y‖ₑ < C} :=
    mem_nhdsWithin_iff.mp (inter_mem (extChartAt_target_mem_nhdsWithin p) hC)
  have hrsub : ball (c p) r ⊆ c.target ∩ {y | ‖d y‖ₑ < C} := by
    simpa using hrsub'
  refine ⟨r,hr,C,hCpos,fun y hy => (hrsub hy).1,?_⟩
  intro y hy z hz
  let η := ContinuousAffineMap.lineMap (R := ℝ) y z
  let γ := c.symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' (c.target ∩ {w | ‖d w‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap, η]
    exact ((convex_ball _ _).segment_subset hy hz).trans hrsub
  simp only [preimage_inter, subset_inter_iff] at hη
  have hηs : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hdist : riemannianEDist 𝓘(ℝ,E) (c.symm y) (c.symm z) ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηs hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hc : mfderiv[Icc 0 1] γ t =
      (mfderiv[Set.range 𝓘(ℝ,E)] c.symm (η t)).comp (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact hηs.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range p))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hcv : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[Set.range 𝓘(ℝ,E)] c.symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($hc 1)
  rw [hcv]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl
end YauCounterexamples

end

end OAI
