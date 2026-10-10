import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoerciveInverse

namespace OAI

/-! Restricting a coercive form and its input to a complete closed subspace. -/

open InnerProductSpace
namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def spectralRestrictedForm (B : E →L[ℝ] E →L[ℝ] ℝ) (S : Submodule ℝ E) :
    S →L[ℝ] S →L[ℝ] ℝ := B.bilinearComp S.subtypeL S.subtypeL

theorem spectralRestrictedForm_coercive (B : E →L[ℝ] E →L[ℝ] ℝ) (S : Submodule ℝ E)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u) :
    IsCoercive (spectralRestrictedForm B S) := by
  refine ⟨c,hc,fun u => ?_⟩
  change c*‖(u : E)‖*‖(u : E)‖ ≤ B u u
  simpa only [pow_two,mul_assoc] using hB u

noncomputable def spectralRestrictedInput (S : Submodule ℝ E) :
    StrongDual ℝ E →L[ℝ] StrongDual ℝ S :=
  (ContinuousLinearMap.compL ℝ S E ℝ).flip S.subtypeL

variable (S : Submodule ℝ E) [CompleteSpace S]

noncomputable def spectralRestrictedInverse (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u) : StrongDual ℝ E →L[ℝ] E :=
  S.subtypeL.comp ((spectralCoerciveInverse (spectralRestrictedForm B S)
    (spectralRestrictedForm_coercive B S c hc hB)).comp (spectralRestrictedInput S))

theorem spectralRestrictedInverse_mem (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u) (F : StrongDual ℝ E) :
    spectralRestrictedInverse S B c hc hB F ∈ S :=
  (spectralCoerciveInverse (spectralRestrictedForm B S)
    (spectralRestrictedForm_coercive B S c hc hB) (spectralRestrictedInput S F)).property

theorem spectralRestrictedInverse_equation (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (F : StrongDual ℝ E) (v : S) : B (spectralRestrictedInverse S B c hc hB F) v=F v :=
  spectralCoerciveInverse_equation (spectralRestrictedForm B S)
    (spectralRestrictedForm_coercive B S c hc hB) (spectralRestrictedInput S F) v

theorem spectralRestrictedInverse_unique (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (F : StrongDual ℝ E) (u : E) (hu : u ∈ S) (he : ∀ v : S, B u v=F v) :
    u=spectralRestrictedInverse S B c hc hB F := by
  exact congrArg Subtype.val (spectralCoerciveInverse_unique (spectralRestrictedForm B S)
    (spectralRestrictedForm_coercive B S c hc hB) (spectralRestrictedInput S F) ⟨u,hu⟩ he)

theorem spectralRestrictedInverse_norm (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u) (F : StrongDual ℝ E) :
    ‖spectralRestrictedInverse S B c hc hB F‖ ≤ ‖F‖/c := by
  have hF : ‖spectralRestrictedInput S F‖ ≤ ‖F‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
    intro v
    exact F.le_opNorm v
  have hBS : ∀ u : S, c*‖u‖^2 ≤ spectralRestrictedForm B S u u := fun u => hB u
  exact (spectralCoerciveInverse_norm (spectralRestrictedForm B S)
    (spectralRestrictedForm_coercive B S c hc hB) c hc hBS
      (spectralRestrictedInput S F)).trans (div_le_div_of_nonneg_right hF hc.le)

end DefocusingNLS

end OAI
