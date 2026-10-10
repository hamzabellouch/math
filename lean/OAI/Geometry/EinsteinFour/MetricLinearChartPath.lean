import OAI.Geometry.EinsteinFour.MetricChartPath

namespace OAI

/-! Path-length comparisons after a fixed linear change of chart
coordinates. These retain the sharp constants supplied by a frozen
orthonormal frame, instead of replacing them by a coarse operator norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem linear_chart_edist_le_pathELength (g : SmoothMetric M) (c : M)
    (A : FourSpace →L[ℝ] FourSpace)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ)
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt FourSpace c).source)
    (K : ℝ≥0)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace I4 (γ t),
      ‖A (mfderiv I4 I4 (chartAt FourSpace c) (γ t) v)‖ₑ ≤
        K * metricTangentENorm g (γ t) v) :
    edist (A (chartAt FourSpace c (γ 0))) (A (chartAt FourSpace c (γ 1))) ≤
      K * (let : RiemannianBundle (TangentSpace I4 : M → Type _) :=
        ⟨g.toRiemannianMetric⟩; Manifold.pathELength I4 γ 0 1) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : ℝ → FourSpace := A ∘ chartAt FourSpace c ∘ γ
  have hc : ContDiffOn ℝ 1 (chartAt FourSpace c ∘ γ) (Icc 0 1) :=
    ((contMDiffOn_chart (I := I4) (n := 1) (x := c)).comp
      hγ.contMDiffOn hsource).contDiffOn
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) := A.contDiff.comp_contDiffOn hc
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖derivWithin η (Icc 0 1) t‖ₑ ≤
        K * ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ := by
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hchart : MDifferentiableAt I4 I4 (chartAt FourSpace c) (γ t) :=
      (contMDiffAt_of_mem_maximalAtlas (n := 1)
        (IsManifold.chart_mem_maximalAtlas c) (hsource t ht)).mdifferentiableAt one_ne_zero
    have he := mfderiv_comp_mfderivWithin t hchart
      (hγ.mdifferentiable one_ne_zero t).mdifferentiableWithinAt hu
    have hlin := A.hasFDerivAt.comp_hasFDerivWithinAt t
      ((hc.differentiableOn one_ne_zero t ht).hasFDerivWithinAt)
    have hlin' := hlin.fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht)
    rw [← fderivWithin_derivWithin]
    change ‖(fderivWithin ℝ (A ∘ (chartAt FourSpace c ∘ γ)) (Icc 0 1) t) 1‖ₑ ≤ _
    rw [hlin', ContinuousLinearMap.comp_apply, ← mfderivWithin_eq_fderivWithin, he]
    change ‖A (mfderiv I4 I4 (chartAt FourSpace c) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1))‖ₑ ≤ _
    exact hK t ht _
  calc
    _ = ‖η 1 - η 0‖ₑ := by rw [edist_eq_enorm_sub, enorm_sub_rev]; rfl
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη zero_le_one
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        (K : ℝ≥0∞) * ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hderiv
    _ = K * Manifold.pathELength I4 γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]

end
end PositiveEinsteinFour.Geometry

end OAI
