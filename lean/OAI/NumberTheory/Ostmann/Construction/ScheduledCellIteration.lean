import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledTransfer
import OAI.NumberTheory.Ostmann.Construction.VariableTransferIteration

namespace OAI

/-! # The finite iteration on the literal shrinking cell schedule -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledCellDiagonal {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg I : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) : ℝ :=
  movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n
    (scheduledSmallLength (cs.drop (n + 1))) m Pg I ρ
    (scheduledRegularPrior cell bulk top (cs.drop (n + 1)) n m) greg ggiant favorable

theorem scheduledCellAmplitude_iteration {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg I : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool)
    (k : ℕ) (hk : 2 ≤ k) (L B₀ cg : ℝ) (hL : 1 ≤ L)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L) (hcg : cg ≤ L) :
    let m := spectatorBulkCount k L
    let η := fun n => scheduledCellAmplitude value outside μ childBound pivotBound V F φ G
      Pg ρ cell bulk top cs n m greg ggiant favorable
    let diag := fun n => scheduledCellDiagonal value outside μ childBound pivotBound V F φ G
      Pg I ρ cell bulk top cs n m greg ggiant favorable
    Real.exp (-B₀ * m) ≤ ‖η 0‖ →
    (∀ n < k, diag n ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ n * m)) →
    (∀ n < k, Real.exp (-cg) * ‖η n‖ ^ 2 ≤ diag n + ‖η (n + 1)‖) →
    ∀ n ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ n * m) ≤ ‖η n‖ := by
  intro m η diag hinit hdiag hstep
  refine variable_transfer_iteration k η diag (fun _ => max 0 cg) B₀ m (Nat.cast_nonneg _)
    (fun _ _ => le_max_left _ _) ?_ hinit hdiag ?_
  · exact spectatorBulkCount_iteration_budget k hk L hL hscale (fun _ => max 0 cg)
      (fun _ _ => max_le (by linarith) hcg)
  · intro n hn
    apply le_trans _ (hstep n hn)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (neg_le_neg (le_max_right 0 cg))

end Ostmann

end OAI
