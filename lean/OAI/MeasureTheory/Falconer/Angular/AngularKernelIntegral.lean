import OAI.MeasureTheory.Falconer.Measures.ProductSchurIntegral
import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalFubini

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularKernelIntegral (a v : ℝ) (Ψ : ℝ → ℝ)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) : ℂ :=
  ((2:ℝ)^(2*(v-a))) • ∫ z, F z
    ∂((sourceAngularShellMeasure v Ψ).prod (sourceArcLength.prod sourceArcLength))

theorem angularKernelIntegral_original (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) (hF : Measurable F)
    {C : ℝ} (hb : ∀ z, ‖F z‖ ≤ C) :
    angularKernelIntegral a v Ψ F = ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength) := by
  have hi : Integrable F ((sourceAngularShellMeasure v Ψ).prod (sourceArcLength.prod sourceArcLength)) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  rw [angularKernelIntegral,integral_prod _ hi]
  have he (r : ℝ) := circle_pair_integral (fun z => F (r,z))
    (hF.comp (measurable_const.prodMk measurable_id)) (fun z => hb (r,z))
  simp_rw [he]
  rw [sourceAngularShellMeasure_integral v hΨ hpos hzero]
  simp only [integral_smul]

theorem angularKernelIntegral_add (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (F G : ℝ × (UnitCircle × UnitCircle) → ℂ) (hF : Measurable F) (hG : Measurable G)
    {C D : ℝ} (hbF : ∀ z, ‖F z‖ ≤ C) (hbG : ∀ z, ‖G z‖ ≤ D) :
    angularKernelIntegral a v Ψ (fun z => F z+G z) =
      angularKernelIntegral a v Ψ F + angularKernelIntegral a v Ψ G := by
  rw [angularKernelIntegral,integral_add
    (Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hbF))
    (Integrable.of_bound hG.aestronglyMeasurable D (Filter.Eventually.of_forall hbG)),smul_add]
  rfl

theorem angularKernelIntegral_smul (a v c : ℝ) (Ψ : ℝ → ℝ)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) :
    angularKernelIntegral a v Ψ (fun z => c • F z) = c • angularKernelIntegral a v Ψ F := by
  simp only [angularKernelIntegral,integral_smul]
  exact smul_comm _ _ _

theorem angularKernelIntegral_outer (a p v c : ℝ) (hc : 0 ≤ c) (Ψ : ℝ → ℝ)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) :
    ‖c • angularKernelIntegral a v Ψ F‖ =
      (2:ℝ)^(2*(p-a))*c*‖angularKernelIntegral p v Ψ F‖ := by
  rw [angularKernelIntegral,angularKernelIntegral,smul_comm c]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-a))),
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  have he : (2:ℝ)^(2*(v-a)) = (2:ℝ)^(2*(p-a))*(2:ℝ)^(2*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [he]
  ring

end PlanarFalconer

end OAI
