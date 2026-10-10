import OAI.Geometry.EinsteinFour.MetricDistance
import Mathlib.Analysis.Calculus.Deriv.AffineMap

namespace OAI

/-! A bounded inverse-chart differential controls the actual Riemannian
distance on a convex chart region. This is the local estimate needed for
finiteness of the metric's Hausdorff volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricEDistance_chart_symm_le (g : SmoothMetric M) (c : M)
    (s : Set FourSpace) (hs : Convex ℝ s) (hst : s ⊆ (chartAt FourSpace c).target)
    (K : ℝ≥0)
    (hK : ∀ z ∈ s, ∀ v : FourSpace,
      metricTangentENorm g ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z v) ≤ K * ‖v‖ₑ)
    (x y : FourSpace) (hx : x ∈ s) (hy : y ∈ s) :
    metricEDistance g ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm y) ≤
      K * edist x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : ℝ →ᴬ[ℝ] FourSpace := ContinuousAffineMap.lineMap x y
  let γ : ℝ → M := (chartAt FourSpace c).symm ∘ η
  have hη : MapsTo η (Icc 0 1) s := by
    rw [mapsTo_iff_image_subset, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hs.segment_subset hx hy
  have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) I4 1 η := by
    rw [contMDiff_iff_contDiff]
    exact η.contDiff
  have hchart : ContMDiffOn I4 I4 1 (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc 0 1) :=
    hchart.comp hηsmooth.contMDiffOn (fun t ht => hst (hη ht))
  have hstart : γ 0 = (chartAt FourSpace c).symm x := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hend : γ 1 = (chartAt FourSpace c).symm y := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ ≤ K * ‖y - x‖ₑ := by
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c).symm (η t) :=
      (contMDiffAt_symm_of_mem_maximalAtlas
        (n := ∞) (IsManifold.chart_mem_maximalAtlas c) (hst (hη ht))).mdifferentiableAt (by simp)
    have hd : mfderivWithin 𝓘(ℝ, ℝ) I4 η (Icc 0 1) t 1 = y - x := by
      have hd' : (fderivWithin ℝ (fun s : ℝ => η s) (Icc 0 1) t) 1 = y - x := by
        rw [fderivWithin_derivWithin]
        exact (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := y)).derivWithin
          (uniqueDiffOn_Icc zero_lt_one t ht)
      simpa only [mfderivWithin_eq_fderivWithin] using! hd'
    have he := mfderiv_comp_mfderivWithin t hc
      (hηsmooth.mdifferentiable (by simp) t).mdifferentiableWithinAt hu
    change ‖mfderivWithin 𝓘(ℝ, ℝ) I4
      ((chartAt FourSpace c).symm ∘ η) (Icc 0 1) t 1‖ₑ ≤ _
    rw [he, ContinuousLinearMap.comp_apply, hd]
    exact hK (η t) (hη ht) (y - x)
  change Manifold.riemannianEDist I4 _ _ ≤ _
  calc
    _ ≤ Manifold.pathELength I4 γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγ hstart hend zero_le_one
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
        ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ :=
      Manifold.pathELength_eq_lintegral_mfderivWithin_Icc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (K : ℝ≥0∞) * ‖y - x‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hspeed
    _ = K * edist x y := by
      simp only [lintegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
        Measure.restrict_apply_univ, mul_one, edist_eq_enorm_sub, enorm_sub_rev]

theorem exists_metric_chart_bound (g : SmoothMetric M) (c : M) :
    ∃ r > (0 : ℝ), ∃ K : ℝ≥0,
      Metric.closedBall (chartAt FourSpace c c) r ⊆ (chartAt FourSpace c).target ∧
      ∀ x ∈ Metric.closedBall (chartAt FourSpace c c) r,
      ∀ y ∈ Metric.closedBall (chartAt FourSpace c c) r,
        metricEDistance g ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm y) ≤
          K * edist x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨K, _hKpos, hK⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt I4 c
  have hK' : ∀ᶠ z in 𝓝 (chartAt FourSpace c c),
      (let L : FourSpace →L[ℝ] TangentSpace I4 ((chartAt FourSpace c).symm z) :=
        mfderiv I4 I4 (chartAt FourSpace c).symm z
       ‖L‖ₑ) < K := by
    simpa only [I4, extChartAt_coe, extChartAt_coe_symm, mfderivWithin_univ,
      ModelWithCorners.range_eq_univ, nhdsWithin_univ, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      Set.range_id] using! hK
  have hc : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem ((chartAt FourSpace c).open_target.mem_nhds hc) hK')
  have hsmall : Metric.closedBall (chartAt FourSpace c c) (r / 2) ⊆
      Metric.ball (chartAt FourSpace c c) r :=
    Metric.closedBall_subset_ball (by linarith)
  have htarget : Metric.closedBall (chartAt FourSpace c c) (r / 2) ⊆
      (chartAt FourSpace c).target := fun z hz => (hball (hsmall hz)).1
  refine ⟨r / 2, by positivity, K, htarget, ?_⟩
  intro x hx y hy
  apply metricEDistance_chart_symm_le g c _ (convex_closedBall _ _) htarget K _ x y hx hy
  intro z hz v
  let L : FourSpace →L[ℝ] TangentSpace I4 ((chartAt FourSpace c).symm z) :=
    mfderiv I4 I4 (chartAt FourSpace c).symm z
  change ‖L v‖ₑ ≤ K * ‖v‖ₑ
  apply (ContinuousLinearMap.le_opENorm L v).trans
  gcongr
  exact (hball (hsmall hz)).2.le

end
end PositiveEinsteinFour.Geometry

end OAI
