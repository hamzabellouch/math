import OAI.Analysis.CircleDomains.Sobolev.SmoothCurveMeasurability
import OAI.Analysis.CircleDomains.Sobolev.CoareaInput

namespace OAI

/-! The smooth scalar differential bounds distinct curve intersections,
including levels modulo one. The bound uses the actual curve image and
is obtained from Lipschitz coarea. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem smooth_curve_mod_one_coarea_bound
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      (μH[0] : Measure ℂ) (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  let L : ℝ → ℝ≥0∞ := fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})
  have hm : AEMeasurable L volume := aemeasurable_smooth_curve_fiber hcoarea hD hA hAD hfin hf
  have hpoint (t : ℝ) :
      (μH[0] : Measure ℂ) (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) ≤
        periodizedLevelLength L t := by
    rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
    exact measure_iUnion_le _
  exact (lintegral_mono hpoint).trans
    ((lintegral_periodizedLevelLength_of_aemeasurable L hm).le.trans
      (smooth_curve_coarea_bound hcoarea hD hA hAD hfin hf))

theorem integrated_smooth_pathImageCount_le_differential
    (hcoarea : PlanarLipschitzFiberCoarea) (γ : C(PathTime, ℂ))
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) (range γ ∩ A) < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t, pathImageCount (A ∩ f ⁻¹' {t}) γ) ≤
      ∫⁻ z in range γ ∩ A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  apply (lintegral_mono (fun t => pathImageCount_le_hausdorffZero (A ∩ f ⁻¹' {t}) γ)).trans
  simp only [← inter_assoc]
  exact smooth_curve_coarea_bound hcoarea hD
    ((isCompact_range γ.continuous).isClosed.measurableSet.inter hA)
    (fun z hz => hAD hz.2) hfin hf

theorem integrated_smooth_circle_pathImageCount_le_differential
    (hcoarea : PlanarLipschitzFiberCoarea) (γ : C(PathTime, ℂ))
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) (range γ ∩ A) < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) γ) ≤
      ∫⁻ z in range γ ∩ A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  apply (lintegral_mono (fun t : ℝ => pathImageCount_le_hausdorffZero
    (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) γ)).trans
  simp only [← inter_assoc]
  exact smooth_curve_mod_one_coarea_bound hcoarea hD
    ((isCompact_range γ.continuous).isClosed.measurableSet.inter hA)
    (fun z hz => hAD hz.2) hfin hf

end CircleDomainRigidity

end

end OAI
