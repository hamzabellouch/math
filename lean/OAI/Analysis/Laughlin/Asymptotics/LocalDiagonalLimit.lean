import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Powerset
import OAI.Analysis.Laughlin.Exterior.ScalingWedge

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

noncomputable def localDiagonals (L Q : ℕ) (A : Finset (Fin (L+1))) : ℝ :=
  ∏ i ∈ A, modeFactor Q i.val

theorem localDiagonals_tendsto (L : ℕ) :
    Tendsto (localDiagonals L) atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  have h : Tendsto (fun Q => ∏ i ∈ A, modeFactor Q i.val) atTop (𝓝 (∏ _i ∈ A, (1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact modeFactor_tendsto i.val
  simpa [localDiagonals] using h

theorem localInverseDiagonals_tendsto (L : ℕ) :
    Tendsto (fun Q => fun A : Finset (Fin (L+1)) => (localDiagonals L Q A)⁻¹)
      atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  simpa using ((tendsto_pi_nhds.mp (localDiagonals_tendsto L)) A).inv₀ (by norm_num)

theorem localMetricDiagonals_tendsto (L : ℕ) :
    Tendsto (fun Q => fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2)
      atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  simpa using ((tendsto_pi_nhds.mp (localInverseDiagonals_tendsto L)) A).pow 2

noncomputable def localDiagonalError (L Q : ℕ) : ℝ :=
  ‖fun A : Finset (Fin (L+1)) => localDiagonals L Q A - 1‖

theorem localDiagonalError_nonneg (L Q : ℕ) : 0 ≤ localDiagonalError L Q := norm_nonneg _

theorem localDiagonalError_tendsto (L : ℕ) :
    Tendsto (localDiagonalError L) atTop (𝓝 0) := by
  have h := ((localDiagonals_tendsto L).sub (tendsto_const_nhds (x := fun _ : Finset (Fin (L+1)) => (1 : ℝ)))).norm
  change Tendsto (fun Q : ℕ => ‖localDiagonals L Q - (fun _ : Finset (Fin (L+1)) => (1 : ℝ))‖) atTop (𝓝 0)
  simpa only [sub_self, norm_zero] using h

theorem localDiagonalError_bound (L Q : ℕ) (A : Finset (Fin (L+1))) :
    |localDiagonals L Q A - 1| ≤ localDiagonalError L Q := by
  simpa only [localDiagonalError, Real.norm_eq_abs] using
    norm_le_pi_norm (fun A : Finset (Fin (L+1)) => localDiagonals L Q A - 1) A

theorem localDiagonalError_quadratic (L Q : ℕ) (ψ : Finset (Fin (L+1)) → ℂ) :
    (∑ A, ‖((localDiagonals L Q A - 1 : ℝ) : ℂ)*ψ A‖^2) ≤
      (localDiagonalError L Q)^2 * ∑ A, ‖ψ A‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A hA
  rw [norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb : ‖((localDiagonals L Q A - 1 : ℝ) : ℂ)‖ ≤ localDiagonalError L Q := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using localDiagonalError_bound L Q A
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end Laughlin.Fock

end OAI
