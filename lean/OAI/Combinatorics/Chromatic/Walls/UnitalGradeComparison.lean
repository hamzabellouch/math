import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductComparison
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGradeAlgebra

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
noncomputable def congr {F F' G G' : Submodule ℚ M} (h : F=G) (h' : F'=G') :
    Grade F F' ≃ₗ[ℚ] Grade G G' := by
  subst G; subst G'
  exact LinearEquiv.refl ℚ _
lemma congr_mk {F F' G G' : Submodule ℚ M} (h : F=G) (h' : F'=G') (x : F) :
    congr h h' (Submodule.Quotient.mk x)=Submodule.Quotient.mk ⟨x.val,h ▸ x.property⟩ := by
  subst G; subst G'; rfl
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearFiltration ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
noncomputable def unitalGradeNonzeroEquiv (d : I → ℕ) (hd : d≠0) (W : ℤ) :
    UnitalSourceGrade a c η hc θ d W ≃ₗ[ℚ] SourceAssociatedGrade a c η hc θ d W :=
  LinearFiltration.congr (unitalSourceFiltration_nonzero a c η hc θ d hd W)
    (unitalSourceFiltration_nonzero a c η hc θ d hd (W+1))
lemma unitalGradeNonzeroEquiv_mk (d : I → ℕ) (hd : d≠0) (W : ℤ)
    (x : unitalSourceFiltration a c η hc θ d W) :
    unitalGradeNonzeroEquiv a c η hc θ d hd W (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk ⟨x.val,(unitalSourceFiltration_nonzero a c η hc θ d hd W) ▸ x.property⟩ :=
  LinearFiltration.congr_mk _ _ _
noncomputable def unitalTensorGradeNonzeroEquiv (d e : I → ℕ) (hd : d≠0) (he : e≠0) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d e W ≃ₗ[ℚ] SourceTensorAssociatedGrade a c η hc θ d e W :=
  LinearFiltration.congr (unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W)
    (unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he (W+1))
lemma unitalTensorGradeNonzeroEquiv_mk (d e : I → ℕ) (hd : d≠0) (he : e≠0) (W : ℤ)
    (x : unitalSourceTensorFiltration a c η hc θ d e W) :
    unitalTensorGradeNonzeroEquiv a c η hc θ d e hd he W (Submodule.Quotient.mk x)=
      LinearFiltration.mk (sourceTensorFiltration a c η hc θ d e W)
        (sourceTensorFiltration a c η hc θ d e (W+1))
        ⟨x.val,(unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W) ▸ x.property⟩ :=
  LinearFiltration.congr_mk _ _ _
lemma unitalGradeCoproduct_nonzero (d e : I → ℕ) (hd : d≠0) (he : e≠0)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (hde : slope c η d=slope c η e) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ (d+e) W) :
    unitalTensorGradeNonzeroEquiv a c η hc θ d e hd he W (unitalGradeCoproduct a c η hc θ d e hs W x)=
      separationCoproduct a c η hc θ d e hde W
        (unitalGradeNonzeroEquiv a c η hc θ (d+e) (add_ne_zero_left _ _ hd) W x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [unitalGradeCoproduct_mk,unitalTensorGradeNonzeroEquiv_mk,unitalGradeNonzeroEquiv_mk,separationCoproduct_mk]
    apply congrArg (LinearFiltration.mk (sourceTensorFiltration a c η hc θ d e W)
      (sourceTensorFiltration a c η hc θ d e (W+1)))
    apply Subtype.ext
    exact unitalSeparationConstant_eq a c η hc d e hs hde x.val
end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
lemma unitalGradeNonzeroEquiv_cast {d e : I → ℕ} (h : d=e) (hd : d≠0) (he : e≠0) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeNonzeroEquiv a c η hc θ e he W (unitalGradeCast a c η hc θ h rfl x)=
      h ▸ unitalGradeNonzeroEquiv a c η hc θ d hd W x := by
  subst e
  rfl
end ElementaryPositivity.RawShuffle

end

end OAI
