import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondFderivScalarComp

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma exists_scalar_inverse_jet {φ : ℝ → ℝ} {v l : ℝ}
    (hφ : ContDiffAt ℝ 2 φ v) (hd : HasDerivAt φ l v) (hl : l≠0) :
    ∃ i : ℝ → ℝ, ContDiffAt ℝ 2 i (φ v) ∧ i (φ v)=v ∧
      HasDerivAt i l⁻¹ (φ v) ∧
      (∀ᶠ w in 𝓝 (φ v),φ (i w)=w) ∧
      iteratedDeriv 2 i (φ v)= -iteratedDeriv 2 φ v/l^3 := by
  let i := hφ.localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hi : ContDiffAt ℝ 2 i (φ v) := hφ.to_localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hiv : i (φ v)=v := hφ.localInverse_apply_image (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hr : ∀ᶠ w in 𝓝 (φ v),φ (i w)=w :=
    (hφ.hasStrictFDerivAt' (hd.hasFDerivAt_equiv hl) (by norm_num)).eventually_right_inverse
  have hiD : HasDerivAt i l⁻¹ (φ v) := (show HasDerivAt φ l (i (φ v)) from hiv.symm ▸ hd).of_local_left_inverse hi.continuousAt hl (by
    simpa only [hiv] using hr)
  refine ⟨i,hi,hiv,hiD,hr,?_⟩
  have hsecond := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (i (φ v)) from hiv.symm ▸ hφ) hi
  have hid : iteratedDeriv 2 (φ ∘ i) (φ v)=0 := by
    have H : (φ ∘ i)=ᶠ[𝓝 (φ v)] (fun w : ℝ => w) := hr
    have H2 := H.deriv.deriv_eq
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id'',deriv_const] using H2
  rw [hid,hiv,hd.deriv,hiD.deriv] at hsecond
  apply (eq_div_iff (pow_ne_zero 3 hl)).mpr
  field_simp at hsecond
  nlinarith only [hsecond]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scalar_inverse_lower_test {φ : ℝ → ℝ} (hmono : StrictMono φ)
    {v F : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ (v x))
    {l : ℝ} (hd : HasDerivAt φ l (v x)) (hl : l≠0)
    (hF : ContDiffAt ℝ 2 F x) (hval : F x=φ (v x))
    (hlo : ∀ᶠ y in 𝓝 x,F y≤φ (v y)) :
    ∃ f : E → ℝ, ContDiffAt ℝ 2 f x ∧ f x=v x ∧
      (∀ᶠ y in 𝓝 x,f y≤v y) ∧
      fderiv ℝ f x=l⁻¹ • fderiv ℝ F x ∧
      ∀ ξ : E, fderiv ℝ (fderiv ℝ f) x ξ ξ=
        l⁻¹*fderiv ℝ (fderiv ℝ F) x ξ ξ-
          (iteratedDeriv 2 φ (v x)/l^3)*(fderiv ℝ F x ξ)^2 := by
  obtain ⟨i,hi,hiv,hiD,hir,hi2⟩ := exists_scalar_inverse_jet hφ hd hl
  let f := i ∘ F
  have hiF : ContDiffAt ℝ 2 i (F x) := hval.symm ▸ hi
  have hiDF : HasDerivAt i l⁻¹ (F x) := hval.symm ▸ hiD
  refine ⟨f,hiF.comp x hF,by dsimp [f]; rw [hval,hiv],?_,?_,?_⟩
  · have hr' := hF.continuousAt.eventually (show ∀ᶠ a in 𝓝 (F x),φ (i a)=a by rwa [hval])
    filter_upwards [hlo,hr'] with y hy hry
    apply hmono.le_iff_le.mp
    simpa only [f,Function.comp_apply,hry] using hy
  · exact (hiDF.comp_hasFDerivAt x (hF.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  · intro ξ
    rw [show f=(fun y => i (F y)) from rfl,second_fderiv_scalar_comp hF hiF ξ,
      hval,hi2,hiD.deriv]
    ring

end WeakMTWTransport

end

end OAI
