import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
namespace Cotype
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem quotient_lift_norm_lt (U : A →L[ℝ] B) (hU : Function.Surjective U)
    {D : ℝ} (hD : 0 ≤ D)
    (hdual : ∀ ψ : B →L[ℝ] ℝ, ‖ψ‖ ≤ D * ‖ψ.comp U‖)
    (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, U a = b ∧ ‖a‖ < D * ‖b‖ + ε := by
  let : IsClosed (U.ker : Set A) := U.isClosed_ker
  let V : (A ⧸ U.ker) →L[ℝ] B := U.ker.liftQL U le_rfl
  have hker : V.ker = ⊥ := Submodule.ker_liftQ_eq_bot U.ker U.toLinearMap le_rfl le_rfl
  have hrange : V.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro b
    obtain ⟨a, rfl⟩ := hU b
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  let e : (A ⧸ U.ker) ≃L[ℝ] B := ContinuousLinearEquiv.ofBijective V hker hrange
  have he (a : A) : e (Submodule.Quotient.mk a) = U a := rfl
  have hq : ‖e.symm b‖ ≤ D * ‖b‖ := by
    obtain ⟨φ, hφ, heval⟩ := exists_dual_vector'' ℝ (e.symm b)
    let ψ : B →L[ℝ] ℝ := φ.comp e.symm.toContinuousLinearMap
    have hψU (a : A) : (ψ.comp U) a = φ (Submodule.Quotient.mk a) := by
      change φ (e.symm (U a)) = _
      rw [← he, e.symm_apply_apply]
    have hψUnorm : ‖ψ.comp U‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro a
      rw [hψU, one_mul]
      exact (φ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans
        (Submodule.Quotient.norm_mk_le U.ker a))
    have hψ : ‖ψ‖ ≤ D := (hdual ψ).trans ((mul_le_mul_of_nonneg_left hψUnorm hD).trans_eq (mul_one D))
    have hv : ψ b = ‖e.symm b‖ := by exact_mod_cast heval
    calc
      _ = ‖ψ b‖ := by rw [hv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖ψ‖ * ‖b‖ := ψ.le_opNorm b
      _ ≤ _ := mul_le_mul_of_nonneg_right hψ (norm_nonneg b)
  obtain ⟨a, ha, hanorm⟩ := Submodule.Quotient.norm_mk_lt (e.symm b) hε
  refine ⟨a, ?_, by linarith⟩
  rw [← he, ha, e.apply_symm_apply]

theorem quotient_lift_norm_le_two (U : A →L[ℝ] B) (hU : Function.Surjective U)
    {D : ℝ} (hD : 0 < D)
    (hdual : ∀ ψ : B →L[ℝ] ℝ, ‖ψ‖ ≤ D * ‖ψ.comp U‖) (b : B) :
    ∃ a : A, U a = b ∧ ‖a‖ ≤ 2 * D * ‖b‖ := by
  by_cases hb : b = 0
  · subst b
    exact ⟨0, map_zero U, by simp⟩
  obtain ⟨a, ha, hanorm⟩ := quotient_lift_norm_lt U hU hD.le hdual b
    (mul_pos hD (norm_pos_iff.mpr hb))
  exact ⟨a, ha, by linarith⟩

end Cotype

end

end OAI
