import OAI.NumberTheory.CubicMoment.Estimates.HeckeCompletedOrder
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

namespace OAI

/-! Decompletion of the actual theta Mellin transform. These algebraic bridges
will be applied to the primitive residue-character theta series. -/
noncomputable section
namespace CubicFirstMoment

def thetaHeckeL (A : ℝ) (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (A:ℂ)^(-s)*(Complex.Gamma s)⁻¹*Λ s

lemma thetaHeckeL_differentiable {A : ℝ} (hA : 0 < A) {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ) : Differentiable ℂ (thetaHeckeL A Λ) := by
  let _ : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  exact (((differentiable_const_cpow_of_neZero (A:ℂ)).comp differentiable_neg).mul
    Complex.differentiable_one_div_Gamma).mul hΛ

lemma thetaHeckeL_completed {A : ℝ} (hA : 0 < A) (Λ : ℂ → ℂ) (s : ℂ)
    (hs : Complex.Gamma s ≠ 0) :
    heckeCompleted A 0 (thetaHeckeL A Λ) s = Λ s := by
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  simp only [heckeCompleted,thetaHeckeL,Complex.ofReal_zero,add_zero,Complex.cpow_neg]
  field_simp

lemma thetaHeckeL_functionalEquation {A : ℝ} (hA : 0 < A)
    (P : WeakFEPair ℂ) (hk : P.k = 1) :
    HeckeFunctionalEquation A 0 P.ε
      (thetaHeckeL A P.Λ) (thetaHeckeL A P.symm.Λ) := by
  intro s hs hdual
  simp only [Complex.ofReal_zero,add_zero] at hs hdual
  rw [thetaHeckeL_completed hA _ _ hs,thetaHeckeL_completed hA _ _ hdual]
  have he := P.functional_equation (1-s)
  simpa only [hk,Complex.ofReal_one,sub_sub_cancel,smul_eq_mul] using he

lemma thetaHeckeL_entire (P : WeakFEPair ℂ) (hP : IsStrongFEPair P)
    {A : ℝ} (hA : 0 < A) :
    Differentiable ℂ (thetaHeckeL A P.Λ) ∧
      Differentiable ℂ (thetaHeckeL A P.symm.Λ) :=
  ⟨thetaHeckeL_differentiable hA hP.differentiable_Λ,
    thetaHeckeL_differentiable hA hP.symm.differentiable_Λ⟩

lemma thetaHeckeL_finiteOrder {A : ℝ} (hA : 0 < A)
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)) :
    CompletedHeckeFiniteOrder A (thetaHeckeL A Λ) := by
  exact ⟨Λ,hΛ,(fun s hs => (thetaHeckeL_completed hA Λ s hs).symm),C,hC,hbound⟩

end CubicFirstMoment

end

end OAI
