import OAI.Analysis.CircleDomains.Topology.VerticalLevelCurve
import OAI.Analysis.CircleDomains.Transfer.LevelChartJacobian
import OAI.Analysis.CircleDomains.Sobolev.CoareaInput
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Exact weighted coarea inside a single regular level chart. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff Classical
noncomputable section
namespace CircleDomainRigidity

def inverseChartWeight (e : OpenPartialHomeomorph ℂ ℂ) (T : Set ℂ)
    (q : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  T.indicator (fun y => q (e.symm y) * ENNReal.ofReal ‖fderiv ℝ e.symm y Complex.I‖)

lemma measurable_inverseChartWeight (e : OpenPartialHomeomorph ℂ ℂ)
    (heI : ContDiffOn ℝ 1 e.symm e.target) {T : Set ℂ} (hT : MeasurableSet T)
    (hTe : T ⊆ e.target) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    Measurable (inverseChartWeight e T q) := by
  let E : ℂ → ℂ := T.piecewise e.symm (fun _ => 0)
  let R : ℂ → ℂ := T.piecewise (fun y => fderiv ℝ e.symm y Complex.I) (fun _ => 0)
  have hE : Measurable E := (heI.continuousOn.mono hTe).measurable_piecewise continuousOn_const hT
  have hR : Measurable R :=
    (((heI.continuousOn_fderiv_of_isOpen e.open_target (by norm_num)).clm_apply continuousOn_const).mono hTe).measurable_piecewise
      continuousOn_const hT
  have h := ((hq.comp hE).mul hR.norm.ennreal_ofReal).indicator hT
  have heq : inverseChartWeight e T q =
      T.indicator (fun y => q (E y) * ENNReal.ofReal ‖R y‖) := by
    funext y
    by_cases hy : y ∈ T <;> simp [inverseChartWeight, E, R, hy]
  rw [heq]
  exact h

lemma inverse_chart_fiber_eq
    {f : ℂ → ℝ} (e : OpenPartialHomeomorph ℂ ℂ) (he : ∀ z, (e z).re = f z)
    (heI : ContDiffOn ℝ 1 e.symm e.target) {T : Set ℂ} (hT : MeasurableSet T)
    (hb : IsBounded T) (hTe : T ⊆ e.target) {q : ℂ → ℝ≥0∞} (hq : Measurable q) (t : ℝ) :
    weightedScalarLevelLength (e.symm '' T) f q t =
      ∫⁻ s, inverseChartWeight e T q (coareaVerticalLine t s) := by
  have hset : (e.symm '' T) ∩ {z | f z = t} =
      (e.symm ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hfy⟩
      have hyr : y.re = t := by
        change f (e.symm y) = t at hfy
        rwa [← he, e.right_inv (hTe hy)] at hfy
      have heqy : coareaVerticalLine t y.im = y := by
        apply Complex.ext <;> simp [hyr]
      exact ⟨y.im, by rwa [mem_preimage, heqy], by simp only [comp_apply, heqy]⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨coareaVerticalLine t s, hs, rfl⟩, ?_⟩
      change f (e.symm (coareaVerticalLine t s)) = t
      rw [← he, e.right_inv (hTe hs), coareaVerticalLine_re]
  rw [weightedScalarLevelLength, hset, weighted_vertical_inverse_curve e heI hT hb hTe t hq]
  rw [← lintegral_indicator (hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable)]
  apply lintegral_congr
  intro s
  by_cases hs : coareaVerticalLine t s ∈ T <;> simp [inverseChartWeight, hs]

lemma inverse_chart_energy_eq
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (e : OpenPartialHomeomorph ℂ ℂ) (heD : e.source ⊆ D)
    (he : ∀ z, (e z).re = f z) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {T : Set ℂ} (hT : MeasurableSet T) (hTe : T ⊆ e.target) (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in e.symm '' T, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) =
      ∫⁻ y, inverseChartWeight e T q y := by
  have hd : ∀ y ∈ T, HasFDerivWithinAt e.symm (fderiv ℝ e.symm y) T y := fun y hy =>
    ((heI.contDiffAt (e.open_target.mem_nhds (hTe hy))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT hd (e.symm.injOn.mono hTe),
    inverseChartWeight, lintegral_indicator hT]
  apply setLIntegral_congr_fun hT
  intro y hy
  dsimp only
  have hj := level_chart_inverse_jacobian hD hf e heD he heI (hTe hy)
  calc
    ENNReal.ofReal |(fderiv ℝ e.symm y).det| *
        (q (e.symm y) * ENNReal.ofReal ‖fderiv ℝ f (e.symm y)‖) =
        q (e.symm y) * ENNReal.ofReal (‖fderiv ℝ f (e.symm y)‖ * |(fderiv ℝ e.symm y).det|) := by
      rw [ENNReal.ofReal_mul (norm_nonneg _)]
      ac_rfl
    _ = _ := by rw [hj]

lemma inverse_chart_weighted_coarea
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (e : OpenPartialHomeomorph ℂ ℂ) (heD : e.source ⊆ D)
    (he : ∀ z, (e z).re = f z) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {T : Set ℂ} (hT : MeasurableSet T) (hb : IsBounded T) (hTe : T ⊆ e.target)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    WeightedScalarCoareaIdentity (e.symm '' T) f q := by
  let W := inverseChartWeight e T q
  have hW : Measurable W := measurable_inverseChartWeight e heI hT hTe hq
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => W (Complex.measurableEquivRealProd.symm p)
  have hH : Measurable H := hW.comp Complex.measurableEquivRealProd.symm.measurable
  have hline (t s : ℝ) : coareaVerticalLine t s = Complex.measurableEquivRealProd.symm (t, s) := by
    apply Complex.ext <;> simp
  have hfun : weightedScalarLevelLength (e.symm '' T) f q = fun t => ∫⁻ s, H (t, s) := by
    funext t
    rw [inverse_chart_fiber_eq e he heI hT hb hTe hq]
    simp only [H, W, hline]
  refine ⟨by rw [hfun]; exact hH.lintegral_prod_right'.aemeasurable, ?_⟩
  rw [hfun, ← lintegral_prod H hH.aemeasurable, ← Measure.volume_eq_prod]
  have hm := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).lintegral_comp hW
  exact hm.trans (inverse_chart_energy_eq hD hf e heD he heI hT hTe q).symm

end CircleDomainRigidity

end

end OAI
