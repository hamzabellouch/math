import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SharpBlockPerturbation
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! The finite coercive inverse needed for the padded four-spin penalty. -/

noncomputable section
namespace ContinuumCoulomb
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem qmaCoerciveInverse_exists (A : E →L[ℝ] E) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ x, g*‖x‖^2 ≤ ⟪x,A x⟫_ℝ) :
    ∃ T : E →L[ℝ] E, (∀ x, A (T x) = x) ∧ (∀ x, T (A x) = x) ∧ ‖T‖ ≤ 1/g := by
  have hi : Function.Injective A := by
    intro x y hxy
    have hz : A (x-y) = 0 := by simp only [map_sub,hxy,sub_self]
    have hh := hgap (x-y)
    rw [hz,inner_zero_right] at hh
    have hn : ‖x-y‖ = 0 := by
      by_contra hn
      have hp : 0 < ‖x-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      exact (not_lt_of_ge hh) (mul_pos hg (sq_pos_of_pos hp))
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective A.toLinearMap
    ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
  let T : E →L[ℝ] E := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hAT (x : E) : A (T x) = x := by
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  have hTA (x : E) : T (A x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  refine ⟨T,hAT,hTA,?_⟩
  apply T.opNorm_le_bound (by positivity)
  intro x
  have hh := hgap (T x)
  rw [hAT] at hh
  have hc := real_inner_le_norm (T x) x
  have hb : g*‖T x‖ ≤ ‖x‖ := by
    by_cases hz : ‖T x‖ = 0
    · rw [hz,mul_zero]
      exact norm_nonneg _
    · have hp : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  calc
    ‖T x‖ ≤ ‖x‖/g := (le_div_iff₀ hg).mpr (by nlinarith)
    _ = (1/g)*‖x‖ := by ring

omit [FiniteDimensional ℝ E] in
theorem qmaInverse_eigenvector (A T : E →L[ℝ] E) (hTA : ∀ x, T (A x) = x)
    (x : E) {c : ℝ} (hc : c ≠ 0) (hx : A x = c • x) : T x = c⁻¹ • x := by
  have h := hTA x
  rw [hx,map_smul] at h
  calc
    T x = c⁻¹ • (c • T x) := by rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
    _ = c⁻¹ • x := by rw [h]

end ContinuumCoulomb

end

end OAI
