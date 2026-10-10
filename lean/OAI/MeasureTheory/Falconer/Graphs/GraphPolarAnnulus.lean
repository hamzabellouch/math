import OAI.MeasureTheory.Falconer.Graphs.GraphProductMeasure
import OAI.MeasureTheory.Falconer.Angular.GraphTorusAngles

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def graphPolarRectangle (a b : ℝ) : Set (ℝ × ℝ) :=
  (Ioo a b) ×ˢ (Ioo (-Real.pi) Real.pi)

theorem graphPolarRectangle_subset {a b : ℝ} (ha : 0 < a) :
    graphPolarRectangle a b ⊆ polarCoord.target := by
  intro p hp
  exact ⟨ha.trans hp.1.1, hp.2⟩

theorem graph_polar_rectangle_integral (f : ℝ × ℝ → ℂ)
    (hf : Continuous f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in polarCoord.symm '' graphPolarRectangle a b,
      (polarCoord x).1⁻¹ • f (polarCoord x)) =
      ∫ φ in (-Real.pi)..Real.pi, ∫ ρ in a..b, f (ρ,φ) := by
  have hS : MeasurableSet (graphPolarRectangle a b) := measurableSet_Ioo.prod measurableSet_Ioo
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ graphPolarRectangle a b) => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    (polarCoord.symm.injOn.mono (graphPolarRectangle_subset ha))
    (fun x => (polarCoord x).1⁻¹ • f (polarCoord x))
  have hcancel : (∫ p in graphPolarRectangle a b,
      |(fderivPolarCoordSymm p).det| • ((polarCoord (polarCoord.symm p)).1⁻¹ •
        f (polarCoord (polarCoord.symm p)))) = ∫ p in graphPolarRectangle a b, f p := by
    apply setIntegral_congr_fun hS
    intro p hp
    have hr := (graphPolarRectangle_subset ha hp).1
    dsimp only
    rw [polarCoord.right_inv (graphPolarRectangle_subset ha hp), det_fderivPolarCoordSymm,
      abs_of_pos hr, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [he, hcancel]
  have hi : Integrable f ((volume.restrict (Ioo a b)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hi' := integral_prod_symm f hi
  rw [Measure.prod_restrict] at hi'
  simpa only [graphPolarRectangle, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo, ← Measure.volume_eq_prod] using hi'

noncomputable def graphPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem graphPlaneEquiv_volume_preserving : MeasurePreserving graphPlaneEquiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp
    ((volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow)

theorem graphPlaneEquiv_norm (x : ℝ × ℝ) :
    ‖graphPlaneEquiv x‖ = (polarCoord x).1 := by
  change ‖(WithLp.toLp 2 ![x.1,x.2] : Plane)‖ = Real.sqrt (x.1^2+x.2^2)
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem graph_plane_rectangle_integral (f : ℝ × ℝ → ℂ)
    (hf : Continuous f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ η in graphPlaneEquiv '' (polarCoord.symm '' graphPolarRectangle a b),
      ‖η‖⁻¹ • f (polarCoord (graphPlaneEquiv.symm η))) =
      ∫ φ in (-Real.pi)..Real.pi, ∫ ρ in a..b, f (ρ,φ) := by
  rw [graphPlaneEquiv_volume_preserving.setIntegral_image_emb graphPlaneEquiv.measurableEmbedding]
  simp only [MeasurableEquiv.symm_apply_apply, graphPlaneEquiv_norm]
  exact graph_polar_rectangle_integral f hf ha hab

end PlanarFalconer

end OAI
