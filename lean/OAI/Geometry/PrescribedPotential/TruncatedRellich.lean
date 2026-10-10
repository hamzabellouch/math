import Mathlib
import OAI.Geometry.PrescribedPotential.FourierKernel
import OAI.Geometry.PrescribedPotential.KernelCompact
import OAI.Geometry.PrescribedPotential.LocalizedCompact

namespace OAI

/-! Truncated Rellich. -/

section

 

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped BoundedContinuousFunction SchwartzMap Classical ComplexInnerProductSpace
namespace EllipticCompact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open SobolevChart

lemma multiply_ae (g : E →ᵇ ℂ) (u : L2 E) :
    multiply g u =ᵐ[volume] fun x => g x * u x := by
  rw [multiply_eq]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (g.memLp_top.toLp g : Lp ℂ ⊤ volume) u,
    (g.memLp_top (μ := volume)).coeFn_toLp] with x h h'
  rw [h, Pi.smul_apply', h', smul_eq_mul]

lemma multiply_toLp (g f : 𝓢(E, ℂ)) :
    multiply g.toBoundedContinuousFunction (f.toLp 2) =
      (SchwartzMap.smulLeftCLM ℂ g f).toLp 2 := by
  apply Lp.ext
  filter_upwards [multiply_ae g.toBoundedContinuousFunction (f.toLp 2),
    f.coeFn_toLp 2 volume, (SchwartzMap.smulLeftCLM ℂ g f).coeFn_toLp 2 volume] with x hm hf hp
  rw [hm, hf, hp, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
  rfl

lemma kernelSection_inner (χ f : 𝓢(E, ℂ)) (x : E) :
    inner ℂ (kernelSection χ x) (f.toLp 2) =
      (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f) : 𝓢(E, ℂ)) x := by
  rw [L2.inner_def]
  conv_rhs => rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [kernelSection_ae χ x, f.coeFn_toLp 2 volume] with y hχ hf
  rw [hχ, hf, RCLike.inner_apply, kernelSectionFun, starRingEnd_apply, star_star,
    SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

def sectionsOn (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport χ)
    (s : Set E) [CompactSpace s] : s →ᵇ (L2 E →L[ℂ] ℂ) :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => innerSL ℂ (kernelSection χ x),
    (innerSL ℂ).continuous.comp ((kernelSection_continuous χ hχ).comp continuous_subtype_val)⟩

lemma sectionsOn_core (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport χ)
    (s : Set E) [CompactSpace s] (f : 𝓢(E, ℂ)) :
    kernelOperator (sectionsOn χ hχ s) (f.toLp 2) =
      (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f) : 𝓢(E, ℂ)).toBoundedContinuousFunction.compContinuous
        ⟨Subtype.val, continuous_subtype_val⟩ := by
  ext x
  change innerSL ℂ (kernelSection χ x) (f.toLp 2) = _
  rw [innerSL_apply_apply]
  exact kernelSection_inner χ f x

lemma localize_sections_core (κ χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport χ)
    (s : Set E) [CompactSpace s] (hs : MeasurableSet s) (hκs : Function.support κ ⊆ s)
    (f : 𝓢(E, ℂ)) :
    localizeL2 κ s hs (kernelOperator (sectionsOn χ hχ s) (f.toLp 2)) =
      (SchwartzMap.smulLeftCLM ℂ κ (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f))).toLp 2 := by
  rw [sectionsOn_core]
  apply Lp.ext
  filter_upwards [localizeL2_restrict κ s hs hκs
    (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f) : 𝓢(E, ℂ)).toBoundedContinuousFunction,
    (SchwartzMap.smulLeftCLM ℂ κ (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f))).coeFn_toLp 2 volume]
    with x h₁ h₂
  rw [h₁, h₂, SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth, smul_eq_mul]
  rfl

lemma truncated_core (κ χ f : 𝓢(E, ℂ)) :
    (multiply κ.toBoundedContinuousFunction ∘L
      fourierInvCLM ℂ (L2 E) ∘L multiply χ.toBoundedContinuousFunction) (f.toLp 2) =
    (SchwartzMap.smulLeftCLM ℂ κ (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f))).toLp 2 := by
  simp only [ContinuousLinearMap.comp_apply, fourierInvCLM_apply]
  exact (congrArg (fun u : L2 E => multiply κ.toBoundedContinuousFunction (𝓕⁻ u))
    (multiply_toLp χ f)).trans
      ((congrArg (multiply κ.toBoundedContinuousFunction)
        (SchwartzMap.toLp_fourierInv_eq (SchwartzMap.smulLeftCLM ℂ χ f))).trans
        (multiply_toLp κ (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ χ f))))

lemma compact_truncated (κ χ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport κ) (hχ : HasCompactSupport χ) :
    IsCompactOperator (multiply κ.toBoundedContinuousFunction ∘L
      fourierInvCLM ℂ (L2 E) ∘L multiply χ.toBoundedContinuousFunction) := by
  let s := tsupport κ
  let : CompactSpace s := isCompact_iff_compactSpace.mp hκ
  have hs : MeasurableSet s := (isClosed_tsupport κ).measurableSet
  let T := (localizeL2 κ s hs).comp (kernelOperator (sectionsOn χ hχ s))
  have hT : IsCompactOperator T :=
    (kernelOperator_compact (sectionsOn χ hχ s)).clm_comp (localizeL2 κ s hs)
  have he : T = multiply κ.toBoundedContinuousFunction ∘L
      fourierInvCLM ℂ (L2 E) ∘L multiply χ.toBoundedContinuousFunction := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) (μ := volume) (by norm_num)).equalizer
      T.continuous (by fun_prop)
    funext f
    exact (localize_sections_core κ χ hχ s hs (subset_tsupport κ) f).trans
      (truncated_core κ χ f).symm
  rw [← he]
  exact hT

end EllipticCompact

end
end

end OAI
