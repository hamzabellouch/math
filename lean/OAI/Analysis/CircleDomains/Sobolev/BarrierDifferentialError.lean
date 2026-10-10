import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! Pointwise differential comparison used by the saved barriers. The
exceptional set allows unrestricted horizontal displacement, while its
energy contribution is charged only on that set. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem composition_covector_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A H : E →L[ℝ] F) (P Q : F →L[ℝ] ℝ) :
    ‖P.comp A-Q.comp H‖ ≤ ‖P‖*‖A-H‖+‖P-Q‖*‖H‖ := by
  have he : P.comp A-Q.comp H = P.comp (A-H)+(P-Q).comp H := by
    ext x
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (P.opNorm_comp_le _) ((P-Q).opNorm_comp_le _))

 theorem barrier_differential_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : Type*} (S : Set X) (A H : X → F)
    (DA DH : X → E →L[ℝ] F) (Φ : F → ℝ)
    {M₁ M₂ e : ℝ} (_hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hbound : ∀ y, ‖fderiv ℝ Φ y‖ ≤ M₁)
    (hlip : ∀ y z, ‖fderiv ℝ Φ y-fderiv ℝ Φ z‖ ≤ M₂*‖y-z‖)
    (hclose : ∀ x ∉ S, ‖A x-H x‖ ≤ e) (x : X) :
    ‖(fderiv ℝ Φ (A x)).comp (DA x)-(fderiv ℝ Φ (H x)).comp (DH x)‖ ≤
      M₁*‖DA x-DH x‖+M₂*e*‖DH x‖+2*M₁*S.indicator (fun _ => ‖DH x‖) x := by
  have hbase := composition_covector_error (DA x) (DH x)
    (fderiv ℝ Φ (A x)) (fderiv ℝ Φ (H x))
  have hfirst : ‖fderiv ℝ Φ (A x)‖*‖DA x-DH x‖ ≤ M₁*‖DA x-DH x‖ :=
    mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    have hd : ‖fderiv ℝ Φ (A x)-fderiv ℝ Φ (H x)‖ ≤ 2*M₁ := by
      exact (norm_sub_le _ _).trans (by linarith [hbound (A x), hbound (H x)])
    have hb := mul_le_mul_of_nonneg_right hd (norm_nonneg (DH x))
    have hz : 0 ≤ M₂*e*‖DH x‖ := mul_nonneg (mul_nonneg hM₂ he) (norm_nonneg _)
    linarith
  · rw [indicator_of_notMem hx, mul_zero, add_zero]
    have hd : ‖fderiv ℝ Φ (A x)-fderiv ℝ Φ (H x)‖ ≤ M₂*e :=
      (hlip _ _).trans (mul_le_mul_of_nonneg_left (hclose x hx) hM₂)
    have hb := mul_le_mul_of_nonneg_right hd (norm_nonneg (DH x))
    linarith

end CircleDomainRigidity

end

end OAI
