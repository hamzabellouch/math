import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorQuotientIncrementBounds
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryFromLogProducts

namespace OAI

/-! # Actual ray trajectories have summable logarithmic increments -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set
open scoped Manifold

/-- Uniform negative heights and polynomial Cartan coordinates give
the actual logarithmic increments needed by the boundary-limit theorem. -/
theorem factor_trajectory_summable_log_increments
    {P N D G E Q J : Type*} [Group N] [Group D] [Group G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [Fintype J]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (K : Set Q)
    {A rate B gap : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate) (hB : 0 ≤ B) (hgap : 0 < gap)
    (p degree : ℕ)
    (hcontract : ∀ d, height d ≤ 0 → ∀ q ∈ K,
      ‖b.equivFun (chart.symm (α d q))‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d))
    (y : P → ℕ → G) (u : P → ℕ → N) (d : P → ℕ → D)
    (hlift : ∀ x n, ι (u x n) * κ (d x n) = y x n)
    (hsize0 : ∀ x n, 0 ≤ size (d x n))
    (hsize : ∀ x n, size (d x n) ≤ B * (1 + (n : ℝ)) ^ degree)
    (hheight : ∀ x n, height (d x n) ≤ -gap * n)
    (hstep : ∀ x n, act ((y x n)⁻¹ * y x (n + 1)) 1 ∈ K) :
    ∃ (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) Q) (a : ℕ → ℝ),
      Summable a ∧ (∀ x n, ‖b.equivFun (X x n)‖ ≤ a n) ∧
      ∀ x n, act (y x (n + 1)) 1 = act (y x n) 1 * Exp (X x n) := by
  let X := fun x n => chart.symm ((act (y x n) 1)⁻¹ * act (y x (n + 1)) 1)
  let a := fun n : ℕ => (A * (1 + B) ^ p) * (1 + (n : ℝ)) ^ (degree * p) *
    Real.exp (-(rate * gap) * n)
  refine ⟨X, a, summable_polynomial_exp_decay _ _ (mul_pos hrate hgap), ?_, ?_⟩
  · intro x n
    exact factor_quotient_increment_polynomial_exp_bound ι κ π α act hact
      (fun q => b.equivFun (chart.symm q)) size height K hA hrate hB hgap p degree
      hcontract n (y x n) (y x (n + 1)) (u x n) (d x n) (hlift x n)
      (hsize0 x n) (hsize x n) (hheight x n) (hstep x n)
  · intro x n
    dsimp only [X]
    rw [← hchart, chart.apply_symm_apply, mul_inv_cancel_left]

end PolycyclicRecognition

end

end OAI
