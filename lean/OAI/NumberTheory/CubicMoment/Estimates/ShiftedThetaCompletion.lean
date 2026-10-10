import OAI.NumberTheory.CubicMoment.Estimates.HeckeThetaCompletion
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeGrowth

namespace OAI

/-! Decompletion with the fixed angular Gamma shift. The normalized heat
kernel has symmetry weight one, so the functional equation remains s ↦ 1-s. -/
noncomputable section
namespace CubicFirstMoment

def shiftedThetaHeckeL (A κ : ℝ) (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (A:ℂ)^(-s)*(Complex.Gamma (s+(κ:ℂ)))⁻¹*Λ s

lemma shiftedThetaHeckeL_differentiable {A κ : ℝ} (hA : 0 < A) {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ) : Differentiable ℂ (shiftedThetaHeckeL A κ Λ) := by
  let _ : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  exact (((differentiable_const_cpow_of_neZero (A:ℂ)).comp differentiable_neg).mul
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (κ:ℂ)))).mul hΛ

lemma shiftedThetaHeckeL_completed {A κ : ℝ} (hA : 0 < A) (Λ : ℂ → ℂ) (s : ℂ)
    (hs : Complex.Gamma (s+(κ:ℂ)) ≠ 0) :
    heckeCompleted A κ (shiftedThetaHeckeL A κ Λ) s = Λ s := by
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  simp only [heckeCompleted,shiftedThetaHeckeL,Complex.cpow_neg]
  field_simp

lemma shiftedThetaHeckeL_functionalEquation {A κ : ℝ} (hA : 0 < A)
    (P : WeakFEPair ℂ) (hk : P.k = 1) :
    HeckeFunctionalEquation A κ P.ε
      (shiftedThetaHeckeL A κ P.Λ) (shiftedThetaHeckeL A κ P.symm.Λ) := by
  intro s hs hdual
  rw [shiftedThetaHeckeL_completed hA _ _ hs,shiftedThetaHeckeL_completed hA _ _ hdual]
  have he := P.functional_equation (1-s)
  simpa only [hk,Complex.ofReal_one,sub_sub_cancel,smul_eq_mul] using he

lemma shiftedThetaHeckeL_finiteOrder {A κ : ℝ} (hA : 0 < A)
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)) :
    ShiftedCompletedHeckeFiniteOrder A κ (shiftedThetaHeckeL A κ Λ) :=
  ⟨Λ,hΛ,(fun s hs => (shiftedThetaHeckeL_completed hA Λ s hs).symm),C,hC,hbound⟩

end CubicFirstMoment

end

end OAI
