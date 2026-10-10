import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryFromLogProducts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts

namespace OAI

/-! # Common compact limits of normalized quotient trajectories -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

/-- The actual trajectory, normalized at its first point, equals the
ordered product of its logarithmic increments. A common summable bound
therefore gives uniform coordinate convergence and a common compact limit set. -/
theorem trajectory_compact_uniform_limit_of_log_increments
    {P E Q J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (f : P → ℕ → Q) (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) Q)
    (a : ℕ → ℝ) (ha : Summable a) (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ a n)
    (hstep : ∀ p n, f p (n + 1) = f p n * Exp (X p n)) :
    ∃ (g : P → Q) (K : Set Q), IsCompact K ∧ (∀ p, g p ∈ K) ∧
      (∀ p, Tendsto (fun n => (f p 0)⁻¹ * f p n) atTop (𝓝 (g p))) ∧
      TendstoUniformly (fun n p => b.equivFun (chart.symm ((f p 0)⁻¹ * f p n)))
        (fun p => b.equivFun (chart.symm (g p))) atTop := by
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨B, hB, hbracket⟩ := exists_basis_structureConstant_bound b
  obtain ⟨g, K, hK, hgK, hg, hu⟩ := exists_compact_uniform_log_product_limit
    dynkin Exp hExp chart hchart hc b hB hbracket X a ha hX
  have hfactor (p : P) (n : ℕ) : f p n = f p 0 * exponentialPartialProduct Exp (X p) n := by
    induction n with
    | zero => simp [exponentialPartialProduct]
    | succ n ih =>
      rw [hstep, ih, exponentialPartialProduct_add Exp (X p) n 1]
      simp [exponentialPartialProduct, mul_assoc]
  have he (p : P) (n : ℕ) : (f p 0)⁻¹ * f p n = exponentialPartialProduct Exp (X p) n := by
    rw [hfactor p n, inv_mul_cancel_left]
  refine ⟨g, K, hK, hgK, ?_, ?_⟩
  · intro p
    simpa only [he] using hg p
  · simpa only [he] using hu

end PolycyclicRecognition

end

end OAI
