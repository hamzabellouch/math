import OAI.Analysis.CircleDomains.Modulus.WeightedCurveLength
import OAI.Analysis.CircleDomains.Transfer.ComplexC1LevelChart

namespace OAI

/-! Vertical parameter curves of a C1 inverse level chart. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def coareaVerticalLine (t s : ℝ) : ℂ := (t : ℂ) + s • Complex.I

@[simp] lemma coareaVerticalLine_re (t s : ℝ) : (coareaVerticalLine t s).re = t := by
  simp [coareaVerticalLine, Complex.real_smul]

@[simp] lemma coareaVerticalLine_im (t s : ℝ) : (coareaVerticalLine t s).im = s := by
  simp [coareaVerticalLine, Complex.real_smul]

lemma coareaVerticalLine_contDiff (t : ℝ) : ContDiff ℝ 1 (coareaVerticalLine t) :=
  contDiff_const.add (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).contDiff

lemma coareaVerticalLine_hasFDerivAt (t s : ℝ) :
    HasFDerivAt (coareaVerticalLine t) (ContinuousLinearMap.toSpanSingleton ℝ Complex.I) s := by
  simpa only [coareaVerticalLine] using!
    (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).hasFDerivAt.const_add (t : ℂ)

lemma coareaVerticalLine_injective (t : ℝ) : Injective (coareaVerticalLine t) := by
  intro a b h
  simpa only [coareaVerticalLine_im] using congrArg Complex.im h

lemma vertical_slice_bounded {T : Set ℂ} (hT : IsBounded T) (t : ℝ) :
    IsBounded ((coareaVerticalLine t) ⁻¹' T) := by
  apply (hT.isCompact_closure.image Complex.continuous_im).isBounded.subset
  intro s hs
  exact ⟨coareaVerticalLine t s, subset_closure hs, coareaVerticalLine_im t s⟩

lemma vertical_inverse_curve_fderiv_norm
    (e : OpenPartialHomeomorph ℂ ℂ) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {t s : ℝ} (hs : coareaVerticalLine t s ∈ e.target) :
    ‖fderiv ℝ (e.symm ∘ coareaVerticalLine t) s‖ =
      ‖fderiv ℝ e.symm (coareaVerticalLine t s) Complex.I‖ := by
  have hd := ((heI.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  rw [(hd.comp s (coareaVerticalLine_hasFDerivAt t s)).fderiv]
  have hn := norm_real_clm_apply
    ((fderiv ℝ e.symm (coareaVerticalLine t s)).comp (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)) 1
  simpa only [abs_one, mul_one, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hn.symm

lemma weighted_vertical_inverse_curve
    (e : OpenPartialHomeomorph ℂ ℂ) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {T : Set ℂ} (hT : MeasurableSet T) (hb : IsBounded T) (hTe : T ⊆ e.target)
    (t : ℝ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in (e.symm ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T), q z ∂μH[1]) =
      ∫⁻ s in (coareaVerticalLine t) ⁻¹' T,
        q (e.symm (coareaVerticalLine t s)) * ENNReal.ofReal ‖fderiv ℝ e.symm (coareaVerticalLine t s) Complex.I‖ := by
  let V := (coareaVerticalLine t) ⁻¹' e.target
  have hV : IsOpen V := e.open_target.preimage (coareaVerticalLine_contDiff t).continuous
  have hcurve : ContDiffOn ℝ 1 (e.symm ∘ coareaVerticalLine t) V :=
    heI.comp (coareaVerticalLine_contDiff t).contDiffOn (fun _ h => h)
  have hd : ∀ s ∈ V, HasStrictFDerivAt (e.symm ∘ coareaVerticalLine t)
      (fderiv ℝ (e.symm ∘ coareaVerticalLine t) s) s := fun s hs =>
    (hcurve.contDiffAt (hV.mem_nhds hs)).hasStrictFDerivAt (by simp)
  have hc := hcurve.continuousOn_fderiv_of_isOpen hV (by simp)
  have hi : InjOn (e.symm ∘ coareaVerticalLine t) V := by
    intro a ha b hb heq
    exact coareaVerticalLine_injective t (e.symm.injOn ha hb heq)
  have hS : MeasurableSet ((coareaVerticalLine t) ⁻¹' T) := hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable
  have hSV : (coareaVerticalLine t) ⁻¹' T ⊆ V := fun _ hs => hTe hs
  rw [weighted_curve_length hV hd hc hi hS (vertical_slice_bounded hb t) hSV hq]
  apply setLIntegral_congr_fun hS
  intro s hs
  dsimp only
  rw [vertical_inverse_curve_fderiv_norm e heI (hTe hs)]
  rfl

end CircleDomainRigidity

end

end OAI
