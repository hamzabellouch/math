import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevParametrix

namespace OAI

/-! Localized Compact. -/

section

 

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped BoundedContinuousFunction SchwartzMap Classical
namespace EllipticCompact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open SobolevChart

def localizedFun (κ : 𝓢(E, ℂ)) (s : Set E) (F : s →ᵇ ℂ) (x : E) : ℂ :=
  if hx : x ∈ s then κ x * F ⟨x, hx⟩ else 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localizedFun_bound (κ : 𝓢(E, ℂ)) (s : Set E) (F : s →ᵇ ℂ) (x : E) :
    ‖localizedFun κ s F x‖ ≤ ‖F‖ * ‖κ x‖ := by
  unfold localizedFun
  split_ifs with hx
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm ⟨x,hx⟩) (norm_nonneg _)
  · simp only [norm_zero]
    positivity

lemma localizedFun_memLp (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) (F : s →ᵇ ℂ) :
    MemLp (localizedFun κ s F) 2 (volume : Measure E) := by
  have hm : StronglyMeasurable (localizedFun κ s F) :=
    (show Continuous (fun x : s => κ x * F x) by fun_prop).stronglyMeasurable.dite
      stronglyMeasurable_const hs
  apply ((κ.memLp (p := 2) (μ := volume)).const_mul (‖F‖ : ℂ)).mono hm.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] using localizedFun_bound κ s F x

def localizedLp (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) (F : s →ᵇ ℂ) :
    L2 E := (localizedFun_memLp κ s hs F).toLp (localizedFun κ s F)

lemma localizedLp_ae (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) (F : s →ᵇ ℂ) :
    localizedLp κ s hs F =ᵐ[volume] localizedFun κ s F :=
  (localizedFun_memLp κ s hs F).coeFn_toLp

lemma localizedLp_norm (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) (F : s →ᵇ ℂ) :
    ‖localizedLp κ s hs F‖ ≤ ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume κ‖ * ‖F‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [localizedLp_ae κ s hs F,
    κ.coeFn_toLp 2 volume] with x hF hκ
  change ‖(localizedLp κ s hs F : E → ℂ) x‖ ≤ ‖F‖ * ‖(κ.toLp 2 : L2 E) x‖
  rw [show (localizedLp κ s hs F : E → ℂ) x = localizedFun κ s F x from hF, hκ]
  exact localizedFun_bound κ s F x

def localizeLinear (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) :
    (s →ᵇ ℂ) →ₗ[ℂ] L2 E where
  toFun := localizedLp κ s hs
  map_add' := by
    intro F G
    apply Lp.ext
    filter_upwards [localizedLp_ae κ s hs (F+G),
      localizedLp_ae κ s hs F,
      localizedLp_ae κ s hs G,
      Lp.coeFn_add (localizedLp κ s hs F) (localizedLp κ s hs G)] with x h hF hG ha
    rw [h, ha, Pi.add_apply, hF, hG]
    simp only [localizedFun]
    split_ifs <;> simp [mul_add]
  map_smul' := by
    intro c F
    apply Lp.ext
    filter_upwards [localizedLp_ae κ s hs (c • F),
      localizedLp_ae κ s hs F,
      Lp.coeFn_smul c (localizedLp κ s hs F)] with x h hF ha
    simp only [RingHom.id_apply]
    rw [h, ha, Pi.smul_apply, hF]
    simp only [localizedFun]
    split_ifs <;> simp [smul_eq_mul, mul_left_comm]

def localizeL2 (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) :
    (s →ᵇ ℂ) →L[ℂ] L2 E :=
  (localizeLinear κ s hs).mkContinuous ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume κ‖
    (localizedLp_norm κ s hs)

lemma localizeL2_ae (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s) (F : s →ᵇ ℂ) :
    localizeL2 κ s hs F =ᵐ[volume] localizedFun κ s F :=
  localizedLp_ae κ s hs F

lemma localizeL2_restrict (κ : 𝓢(E, ℂ)) (s : Set E) (hs : MeasurableSet s)
    (hκ : Function.support κ ⊆ s) (F : E →ᵇ ℂ) :
    localizeL2 κ s hs (F.compContinuous ⟨Subtype.val, continuous_subtype_val⟩) =ᵐ[volume]
      fun x => κ x * F x := by
  filter_upwards [localizeL2_ae κ s hs (F.compContinuous ⟨Subtype.val, continuous_subtype_val⟩)] with x hx
  rw [hx, localizedFun]
  split_ifs with h
  · rfl
  · have hk : κ x = 0 := not_not.mp (mt (fun hne : κ x ≠ 0 => hκ hne) h)
    rw [hk, zero_mul]

end EllipticCompact

end
end

end OAI
