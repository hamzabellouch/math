import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGrade

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
noncomputable def gradeTopBotEquiv : Grade (⊤ : Submodule ℚ M) ⊥ ≃ₗ[ℚ] M :=
  ((next (⊤ : Submodule ℚ M) ⊥).quotEquivOfEqBot (by
    ext x
    simp [next])).trans (Submodule.topEquiv)

lemma grade_same_subsingleton (F : Submodule ℚ M) : Subsingleton (Grade F F) := by
  have h : next F F=⊤ := by ext x; simp [next]
  change Subsingleton (F ⧸ next F F)
  rw [h]
  infer_instance
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
noncomputable def zeroPolynomialEquiv : S (0 : I → ℕ) ≃ₗ[ℚ] ℚ where
  toFun f := constantCoeff f.val
  invFun r := r • (1 : S (0 : I → ℕ))
  left_inv := fun f=>(S_zero_eq_scalar f).symm
  right_inv := by intro r; simp
  map_add' f g := by simp
  map_smul' r f := by simp

noncomputable def zeroQuotientEquiv (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    B a μ 0 ≃ₗ[ℚ] ℚ :=
  ((destabilizingSpace a μ 0).quotEquivOfEqBot (destabilizingSpace_zero a μ)).trans zeroPolynomialEquiv

lemma unitalSourceFiltration_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (W : ℤ) : unitalSourceFiltration a c η hc θ (0 : I → ℕ) W=
      if W≤0 then ⊤ else ⊥ := by
  unfold unitalSourceFiltration
  exact ite_eq_left (rfl : (0 : I → ℕ)=0)

noncomputable def zeroUnitalGradeEquiv (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) : UnitalSourceGrade a c η hc θ 0 0 ≃ₗ[ℚ] ℚ := by
  change Grade (unitalSourceFiltration a c η hc θ 0 0)
    (unitalSourceFiltration a c η hc θ 0 (0+1)) ≃ₗ[ℚ] ℚ
  rw [unitalSourceFiltration_zero,unitalSourceFiltration_zero]
  exact (gradeTopBotEquiv (M:=B a (slope c η) 0)).trans (zeroQuotientEquiv a (slope c η))

lemma zeroUnitalGrade_subsingleton (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (W : ℤ) (hW : W≠0) : Subsingleton (UnitalSourceGrade a c η hc θ 0 W) := by
  unfold UnitalSourceGrade
  by_cases hw : W≤0
  · have hw' : W+1≤0 := by omega
    simpa [unitalSourceFiltration_zero,hw,hw'] using
      grade_same_subsingleton (⊤ : Submodule ℚ (B a (slope c η) 0))
  · have hw' : ¬W+1≤0 := by omega
    simpa [unitalSourceFiltration_zero,hw,hw'] using
      grade_same_subsingleton (⊥ : Submodule ℚ (B a (slope c η) 0))
end ElementaryPositivity.RawShuffle

end

end OAI
