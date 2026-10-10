import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! Smoothness of the actual Coulomb kernel away from its pole, with
uniform derivative bounds on the fixed annulus used in cell estimates. -/

noncomputable section
open scoped ContDiff BigOperators Classical
namespace ContinuumCoulomb

theorem coulombKernel_contDiffAt {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ Coulomb.coulombKernel x := by
  exact (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

theorem coulombKernel_iteratedFDeriv_continuousAt (k : ℕ) {x : Position} (hx : x ≠ 0) :
    ContinuousAt (iteratedFDeriv ℝ k Coulomb.coulombKernel) x :=
  ((coulombKernel_contDiffAt hx).differentiableAt_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).continuousAt

theorem coulombKernel_fixed_annulus_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : Fin 5, ∀ x : Position, 1/2 ≤ ‖x‖ → ‖x‖ ≤ 2 →
      ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖ ≤ C := by
  let K := Metric.closedBall (0:Position) 2 \ Metric.ball 0 (1/2)
  have hK : IsCompact K := (isCompact_closedBall (0:Position) 2).diff Metric.isOpen_ball
  have hk (k : Fin 5) : ContinuousOn (iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel) K := by
    intro x hx
    apply (coulombKernel_iteratedFDeriv_continuousAt k ?_).continuousWithinAt
    intro he
    have hn := hx.2
    apply hn
    rw [he,Metric.mem_ball,dist_self]
    norm_num
  choose C hC using fun k : Fin 5 => hK.exists_bound_of_continuousOn (hk k)
  refine ⟨1+∑ k, |C k|,?_,fun k x hx₁ hx₂ => ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  · have hx : x ∈ K := by
      refine ⟨?_,?_⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using hx₂
      · simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx₁
    have hb := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
      abs_nonneg (C j)) (Finset.mem_univ k)
    exact (hC k x hx).trans ((le_abs_self _).trans (by linarith))

end ContinuumCoulomb

end

end OAI
