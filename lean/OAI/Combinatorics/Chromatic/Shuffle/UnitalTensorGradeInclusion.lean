import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalShuffleCoproduct

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

lemma tensorGradeEquiv_lof (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) (x : TensorGradePart F G W u) :
    tensorGradeEquiv F G hF hG W (DirectSum.lof ℚ ℤ (TensorGradePart F G W) u x)=
      tensorGradeInclusionW F G W u x := by
  change DirectSum.toModule ℚ ℤ _ _ _=_
  rw [DirectSum.toModule_lof]

lemma tensorGradeEquiv_symm_inclusion (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) (x : TensorGradePart F G W u) :
    (tensorGradeEquiv F G hF hG W).symm (tensorGradeInclusionW F G W u x)=
      DirectSum.lof ℚ ℤ (TensorGradePart F G W) u x := by
  apply (tensorGradeEquiv F G hF hG W).injective
  rw [LinearEquiv.apply_symm_apply,tensorGradeEquiv_lof]

lemma tensorGrade_induction (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W : ℤ) (P : TensorGrade F G W → Prop)
    (hz : P 0) (ha : ∀ x y,P x → P y → P (x+y))
    (ht : ∀ u (x : Grade (F u) (F (u+1))) (y : Grade (G (W-u)) (G (W-u+1))),
      P (tensorGradeInclusionW F G W u (x⊗ₜ[ℚ]y))) (x : TensorGrade F G W) : P x := by
  obtain ⟨z,rfl⟩ := (tensorGradeEquiv F G hF hG W).surjective x
  induction z using DirectSum.induction_on with
  | zero => simpa only [map_zero] using hz
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy
  | of u z =>
    change P (tensorGradeEquiv F G hF hG W (DirectSum.lof ℚ ℤ (TensorGradePart F G W) u z))
    rw [tensorGradeEquiv_lof]
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact ha _ _ hx hy
    | tmul x y => exact ht u x y
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def unitalTensorGradeInclusionW (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ) (W u : ℤ) :
    UnitalSourceGrade a c η hc θ d u ⊗[ℚ] UnitalSourceGrade a c η hc θ e (W-u) →ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ d e W :=
  tensorGradeInclusionW (unitalSourceFiltration a c η hc θ d)
    (unitalSourceFiltration a c η hc θ e) W u

lemma unitalTensorGrade_induction (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (P : UnitalSourceTensorGrade a c η hc θ d e W → Prop)
    (hz : P 0) (ha : ∀ x y,P x → P y → P (x+y))
    (ht : ∀ u (x : UnitalSourceGrade a c η hc θ d u)
      (y : UnitalSourceGrade a c η hc θ e (W-u)),
      P (unitalTensorGradeInclusionW a c η hc θ d e W u (x⊗ₜ[ℚ]y)))
    (x : UnitalSourceTensorGrade a c η hc θ d e W) : P x :=
  tensorGrade_induction _ _ (unitalSourceFiltration_antitone a c η hc θ d)
    (unitalSourceFiltration_antitone a c η hc θ e) W P hz ha ht x

lemma globalTensorGradeInclusion_part (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W u : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val u)
    (y : UnitalSourceGrade a c η hc θ e.val (W-u)) :
    globalTensorGradeInclusion a c η hc θ d e W
      (unitalTensorGradeInclusionW a c η hc θ d.val e.val W u (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u) x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,W-u) y := by
  change DirectSum.toModule ℚ ℤ _ _ ((unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm
    (tensorGradeInclusionW _ _ W u (x⊗ₜ[ℚ]y)))=_
  rw [show (unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm
      (tensorGradeInclusionW _ _ W u (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ ℤ _ u (x⊗ₜ[ℚ]y) from tensorGradeEquiv_symm_inclusion _ _ _ _ W u _]
  rw [DirectSum.toModule_lof]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
