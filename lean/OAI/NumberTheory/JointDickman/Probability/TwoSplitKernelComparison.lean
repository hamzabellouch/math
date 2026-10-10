import OAI.NumberTheory.JointDickman.Probability.FiniteChannelSchur
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail

namespace OAI

/-!
# Operator comparison for the actual and independent two-split laws

The output cells may be any finite collection of sets of positive integers.
Their common measure `m` is kept explicit. The estimates thus apply to the
logarithm/residue cells in the paper without choosing a particular mesh.
-/

namespace JointDickman

open Finset

noncomputable def uniformProbabilityKernel {A : Type*} (m : ℝ)
    (q : A → A → ℝ) (a b : A) : ℝ := q a b / (m * m)

/-- A uniform cell probability error gives the corresponding square-norm
operator error after division by the cell measures. -/
theorem uniformProbabilityKernel_error {A : Type*} [Fintype A]
    {m δ : ℝ} (hm : 0 < m) (hδ : 0 ≤ δ) (q r : A → A → ℝ)
    (hqr : ∀ a b, |q a b - r a b| ≤ δ) (g : A → ℝ) :
    (∑ a, m * (finiteKernelAction (fun _ => m)
      (fun a b => uniformProbabilityKernel m q a b - uniformProbabilityKernel m r a b) g a) ^ 2) ≤
      ((Fintype.card A : ℝ) * δ / m) ^ 2 * ∑ a, m * g a ^ 2 := by
  let K := fun a b => uniformProbabilityKernel m q a b - uniformProbabilityKernel m r a b
  have hentry (a b : A) : m * |K a b| ≤ δ / m := by
    have heq : m * |K a b| = |q a b - r a b| / m := by
      dsimp [K, uniformProbabilityKernel]
      rw [← sub_div, abs_div, abs_of_pos (mul_pos hm hm)]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (hqr a b) hm.le
  have hrow (a : A) : (∑ b, m * |K a b|) ≤ (Fintype.card A : ℝ) * δ / m := by
    calc
      _ ≤ ∑ _b : A, δ / m := sum_le_sum fun b _ => hentry a b
      _ = _ := by simp [mul_div_assoc]
  have hcol (b : A) : (∑ a, m * |K a b|) ≤ (Fintype.card A : ℝ) * δ / m := by
    calc
      _ ≤ ∑ _a : A, δ / m := sum_le_sum fun a _ => hentry a b
      _ = _ := by simp [mul_div_assoc]
  exact finiteKernelAction_square_bound (fun _ => m) K (fun _ => hm.le)
    (by positivity) hrow hcol g

open Classical in
noncomputable def actualTwoSplitCellMass {A : Type*} (Q : Finset ℕ)
    (cells : A → Set ℕ) (a b : A) : ℝ :=
  ∑ x, if (actualSplitProducts Q x).1 ∈ cells a ∧ (actualSplitProducts Q x).2 ∈ cells b then
    sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0

open Classical in
noncomputable def independentTwoSplitCellMass {A : Type*} (Q : Finset ℕ)
    (cells : A → Set ℕ) (a b : A) : ℝ :=
  ∑ y, if (independentSplitProducts Q y).1 ∈ cells a ∧
      (independentSplitProducts Q y).2 ∈ cells b then
    bernoulliProductMass univ (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0

/-- The two-split kernel replacement, for the actual prime products and
any finite collection of output cells. -/
theorem twoSplitKernel_error {A : Type*} [Fintype A] (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cells : A → Set ℕ) {m : ℝ} (hm : 0 < m)
    (g : A → ℝ) :
    (∑ a, m * (finiteKernelAction (fun _ => m)
      (fun a b => uniformProbabilityKernel m (actualTwoSplitCellMass Q cells) a b -
        uniformProbabilityKernel m (independentTwoSplitCellMass Q cells) a b) g a) ^ 2) ≤
      ((Fintype.card A : ℝ) * (9 / (8 * N : ℝ)) / m) ^ 2 * ∑ a, m * g a ^ 2 := by
  apply uniformProbabilityKernel_error hm (by positivity)
  intro a b
  exact twoSplitPrimeProducts_cell_tail_bound Q hQ hN hcut (cells a) (cells b)

end JointDickman

end OAI
