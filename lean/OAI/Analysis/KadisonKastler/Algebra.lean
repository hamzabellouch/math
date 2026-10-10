import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-!
# Norm topology on concrete von Neumann algebras

The bicommutant definition used by Mathlib implies norm closedness directly.
This supplies the complete C*-algebra structures needed for matrix norms and
for the perturbation maps in the manuscript's UCP criterion.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isClosed_algebra (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

/-- The ordinary complete C*-algebra underlying the concrete algebra. -/
abbrev Algebra (M : VonNeumannAlgebra H) := M.toStarSubalgebra

noncomputable instance algebraCStarAlgebra (M : VonNeumannAlgebra H) :
    CStarAlgebra (Algebra M) :=
  StarSubalgebra.cstarAlgebra M.toStarSubalgebra (h_closed := isClosed_algebra M)

theorem isClosed_unitBall (M : VonNeumannAlgebra H) : IsClosed (unitBall M) :=
  (isClosed_algebra M).inter (isClosed_le continuous_norm continuous_const)

/-- Unlike arbitrary nonclosed sets, concrete algebra unit balls are
determined by their Hausdorff distance. -/
theorem eq_of_kkDistance_eq_zero {M N : VonNeumannAlgebra H}
    (h : kkDistance M N = 0) : M = N := by
  have hballs : unitBall M = unitBall N := by
    exact ((isClosed_unitBall M).hausdorffDist_zero_iff_eq
      (isClosed_unitBall N) (unitBall_hausdorffEDist_ne_top M N)).mp h
  apply VonNeumannAlgebra.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hscaled : ‖(‖x‖⁻¹ : ℂ) • x‖ ≤ 1 := by
    simp [norm_smul, Complex.norm_real, inv_mul_cancel₀ hn.ne']
  have hm : (‖x‖⁻¹ : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hn.ne'
  constructor
  · intro hxM
    have hu : (‖x‖⁻¹ : ℂ) • x ∈ unitBall M :=
      ⟨M.toStarSubalgebra.smul_mem hxM _, hscaled⟩
    rw [hballs] at hu
    exact (N.toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem_iff hm).mp hu.1
  · intro hxN
    have hu : (‖x‖⁻¹ : ℂ) • x ∈ unitBall N :=
      ⟨N.toStarSubalgebra.smul_mem hxN _, hscaled⟩
    rw [← hballs] at hu
    exact (M.toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem_iff hm).mp hu.1

end KadisonKastler

end OAI
