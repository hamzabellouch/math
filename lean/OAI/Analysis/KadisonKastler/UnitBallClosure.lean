import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Topology.Algebra.StarSubalgebra

namespace OAI

/-! # Unit balls in norm closures of complex linear subspaces

Radial contraction keeps approximants in their original subspace. It
proves the norm-density statement needed for the separable test algebras.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

def unitBallClip (x : B) : B := (((max 1 ‖x‖)⁻¹ : ℝ) : ℂ) • x

theorem unitBallClip_norm_le (x : B) : ‖unitBallClip x‖ ≤ 1 := by
  have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [unitBallClip, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_eq_div]
  exact (div_le_one hp).mpr (le_max_right _ _)

theorem unitBallClip_eq_self {x : B} (hx : ‖x‖ ≤ 1) : unitBallClip x = x := by
  simp only [unitBallClip, max_eq_left hx, inv_one, Complex.ofReal_one, one_smul]

theorem continuous_unitBallClip : Continuous (unitBallClip : B → B) := by
  have hc : Continuous (fun x : B => (max 1 ‖x‖)⁻¹) :=
    (continuous_const.max continuous_norm).inv₀ (fun x => by
      have h : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      exact ne_of_gt h)
  exact (Complex.continuous_ofReal.comp hc).smul continuous_id

theorem unitBallClip_mem (S : Submodule ℂ B) {x : B} (hx : x ∈ S) :
    unitBallClip x ∈ S := S.smul_mem _ hx

/-- The unit ball of a linear subspace is norm dense in the unit ball of
its closure, even when the subspace is not closed. -/
theorem closure_submodule_unitBall (S : Submodule ℂ B) :
    closure {x : B | x ∈ S ∧ ‖x‖ ≤ 1} =
      {x : B | x ∈ closure (S : Set B) ∧ ‖x‖ ≤ 1} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx
      exact ⟨subset_closure hx.1, hx.2⟩
    · exact isClosed_closure.inter (isClosed_le continuous_norm continuous_const)
  · intro x hx
    have hclip := mem_closure_image continuous_unitBallClip.continuousAt hx.1
    rw [unitBallClip_eq_self hx.2] at hclip
    apply closure_mono _ hclip
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨unitBallClip_mem S hy, unitBallClip_norm_le y⟩

end

end KadisonKastler

end OAI
