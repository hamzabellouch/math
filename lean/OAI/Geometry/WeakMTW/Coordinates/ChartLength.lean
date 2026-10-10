import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalLength
import OAI.Geometry.WeakMTW.Coordinates.ChartMetric

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold

namespace ChartMetric
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
theorem chartLift_eq_mfderiv_symm (x : M) {y : E} (hy : y ∈ (chartAt E x).target) :
    chartLift x y = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y := by
  have h := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, E))
    ((chartAt E x).map_target hy)
  simp only [mfld_simps] at h
  dsimp only [chartLift]
  convert! h using 1
  rw [(chartAt E x).right_inv hy]

theorem sqrt_metric_eq_norm (x : M) {y : E} (hy : y ∈ (chartAt E x).target) (v : E) :
    Real.sqrt (metric x y v v) =
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y v‖ := by
  rw [metric_apply, chartLift_eq_mfderiv_symm x hy]
  exact (@norm_eq_sqrt_real_inner
    (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))
    (inferInstance : SeminormedAddCommGroup (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y)))
    (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))) _).symm

 theorem coordinateLength_eq_pathELength (x : M) {c : ℝ → E} {a b : ℝ}
    (hc : ContDiffOn ℝ 1 c (Icc a b))
    (hct : ∀ t ∈ Icc a b, c t ∈ (chartAt E x).target) :
    NormalNeighborhood.NormalFlow.coordinateLength (metric x) c a b =
      pathELength 𝓘(ℝ, E) ((chartAt E x).symm ∘ c) a b := by
  rw [NormalNeighborhood.NormalFlow.coordinateLength, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hd := ((hc t ht').contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hmc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t :=
    mdifferentiableAt_iff_differentiableAt.mpr hd
  have hms := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E)) (chart_mem_atlas E x) (hct t ht')
  rw [sqrt_metric_eq_norm x (hct t ht'), mfderiv_comp t hms hmc]
  simp only [mfderiv_eq_fderiv, ofReal_norm]
  rfl

end
end ChartMetric
end

end WeakMTWGlobalSupport

end OAI
