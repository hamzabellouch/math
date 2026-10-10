import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakFluxPrimitive

namespace OAI

/-! Localize the weak-flux primitive strictly inside the radial domain. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralLocalFlux_primitive (R a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < R)
    (F G : ℝ → ℂ) (hF : LocallyIntegrableOn F (Ioo 0 R))
    (hG : ContinuousOn G (Ioo 0 R))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 R → (∫ x, deriv φ x • F x)=-(∫ x, φ x • G x)) :
    ∃ P : ℝ → ℂ, (∀ x ∈ Ioo a b, HasDerivAt P (G x) x) ∧
      ∀ᵐ x, x ∈ Ioo a b → F x=P x := by
  have hsub : Icc a b ⊆ Ioo 0 R := fun x hx => ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  let clamp := fun x : ℝ => max a (min b x)
  have hclamp (x : ℝ) : clamp x ∈ Icc a b :=
    ⟨le_max_left _ _,max_le hab.le (min_le_left _ _)⟩
  have hfix (x : ℝ) (hx : x ∈ Icc a b) : clamp x=x := by
    dsimp only [clamp]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  let F₀ := (Icc a b).indicator F
  let G₀ := fun x => G (clamp x)
  have hF₀ : LocallyIntegrable F₀ := by
    apply Integrable.locallyIntegrable
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (hF.integrableOn_compact_subset hsub isCompact_Icc)
  have hG₀ : Continuous G₀ :=
    hG.comp_continuous (by fun_prop) (fun x => hsub (hclamp x))
  obtain ⟨P,hP,he⟩ := spectralWeakFlux_primitive a b hab F₀ G₀ hF₀ hG₀ (by
    intro φ hφ hφc hφs
    have hFtest : (fun x => deriv φ x • F₀ x)=(fun x => deriv φ x • F x) := by
      funext x
      by_cases hx : x ∈ Icc a b
      · simp only [F₀,indicator_of_mem hx]
      · have hzero : deriv φ x=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (hφs (tsupport_deriv_subset h)))
        simp only [hzero,zero_smul]
    have hGtest : (fun x => φ x • G₀ x)=(fun x => φ x • G x) := by
      funext x
      by_cases hx : x ∈ Icc a b
      · simp only [G₀,hfix x hx]
      · have hzero : φ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
        simp only [hzero,zero_smul]
    rw [hFtest,hGtest]
    exact hw φ hφ hφc (hφs.trans hsub))
  refine ⟨P,fun x hx => ?_,?_⟩
  · simpa only [G₀,hfix x ⟨hx.1.le,hx.2.le⟩] using hP x
  · filter_upwards [he] with x hx hxab
    have h := hx hxab
    simpa only [F₀,indicator_of_mem (show x ∈ Icc a b from ⟨hxab.1.le,hxab.2.le⟩)] using h

end DefocusingNLS

end OAI
