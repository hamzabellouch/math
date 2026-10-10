import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace OAI

/-! Inverting the varying weighted coercive forms in the radial limit argument. -/

open InnerProductSpace
namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def spectralCoerciveInverse (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) :
    StrongDual ℝ E →L[ℝ] E :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem spectralCoerciveInverse_equation (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (F : StrongDual ℝ E) (v : E) : B (spectralCoerciveInverse B hB F) v=F v := by
  have h := hB.continuousLinearEquivOfBilin_apply (spectralCoerciveInverse B hB F) v
  change inner ℝ (hB.continuousLinearEquivOfBilin
    (hB.continuousLinearEquivOfBilin.symm ((toDual ℝ E).symm F))) v=_ at h
  rw [ContinuousLinearEquiv.apply_symm_apply,toDual_symm_apply] at h
  exact h.symm

theorem spectralCoerciveInverse_unique (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (F : StrongDual ℝ E) (u : E) (hu : ∀ v, B u v=F v) :
    u=spectralCoerciveInverse B hB F := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply,hB.continuousLinearEquivOfBilin_apply,
    spectralCoerciveInverse_equation,hu]

theorem spectralCoerciveInverse_norm (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B)
    (c : ℝ) (hc : 0 < c) (hbound : ∀ u, c*‖u‖^2 ≤ B u u) (F : StrongDual ℝ E) :
    ‖spectralCoerciveInverse B hB F‖ ≤ ‖F‖/c := by
  let u := spectralCoerciveInverse B hB F
  have he := spectralCoerciveInverse_equation B hB F u
  have hb := hbound u
  have hf : F u ≤ ‖F‖*‖u‖ := (le_abs_self _).trans (F.le_opNorm u)
  apply (le_div_iff₀ hc).2
  by_cases hu : ‖u‖=0
  · change ‖u‖*c ≤ ‖F‖
    rw [hu,zero_mul]
    exact norm_nonneg F
  · have hu0 := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    change ‖u‖*c ≤ ‖F‖
    nlinarith

end DefocusingNLS

end OAI
