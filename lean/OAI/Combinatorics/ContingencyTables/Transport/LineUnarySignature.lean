import OAI.Combinatorics.ContingencyTables.Transport.LaminarSignature

namespace OAI

/-!
# The line and unary factors of the bounded-table application

The bounded-table signature argument uses disjoint row/column line factors
and unary tree penalties. Factoring the product after two removals expresses
unary factors as nonnegative diagonal corrections of the line kernel.
-/

namespace ContingencyTables

open scoped BigOperators

section Products

variable {A : Type*} [Fintype A] [DecidableEq A]

def productTwoUpdates (a₀ a₁ a₂ : A → ℝ) (i j : A) : ℝ :=
  ∏ k, if k = i then (if k = j then a₂ k else a₁ k)
    else (if k = j then a₁ k else a₀ k)

/-- Exact factorization of the actual product after two coordinate changes,
including a repeated change of the same coordinate. -/
theorem productTwoUpdates_factor (a₀ a₁ a₂ : A → ℝ)
    (h₀ : ∀ k, a₀ k ≠ 0) (h₁ : ∀ k, a₁ k ≠ 0) (i j : A) :
    productTwoUpdates a₀ a₁ a₂ i j =
      (∏ k, a₀ k) * (a₁ i / a₀ i) * (a₁ j / a₀ j) *
        (if i = j then a₀ i * a₂ i / (a₁ i) ^ 2 else 1) := by
  have hterm (k : A) :
      (if k = i then (if k = j then a₂ k else a₁ k)
        else (if k = j then a₁ k else a₀ k)) =
      a₀ k * (if k = i then a₁ k / a₀ k else 1) *
        (if k = j then a₁ k / a₀ k else 1) *
        (if k = i ∧ i = j then a₀ k * a₂ k / (a₁ k) ^ 2 else 1) := by
    by_cases hi : k = i
    · subst k
      by_cases hij : i = j
      · subst j
        simp only [ite_true, and_self]
        field_simp [h₀ i, h₁ i]
      · simp only [ite_true, hij, ite_false, and_false, mul_one]
        field_simp [h₀ i]
    · by_cases hj : k = j
      · subst k
        simp only [hi, ite_false, ite_true, false_and, mul_one]
        field_simp [h₀ j]
      · simp [hi, hj]
  unfold productTwoUpdates
  simp_rw [hterm, Finset.prod_mul_distrib]
  have hlast : (∏ k, if k = i ∧ i = j then a₀ k * a₂ k / (a₁ k) ^ 2 else 1) =
      if i = j then a₀ i * a₂ i / (a₁ i) ^ 2 else 1 := by
    by_cases h : i = j <;> simp [h]
  rw [hlast]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]

end Products

section LineUnary

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- Values of every line factor and every unary factor after zero, one,
and two removals give exactly this two-removal matrix. -/
def lineUnaryRemoval (line : I → G) (a₀ a₁ a₂ : G → ℝ) (b₀ b₁ b₂ : I → ℝ) :
    Matrix I I ℝ := fun i j =>
  productTwoUpdates a₀ a₁ a₂ (line i) (line j) * productTwoUpdates b₀ b₁ b₂ i j

theorem lineUnaryRemoval_factor (line : I → G) (a₀ a₁ a₂ : G → ℝ) (b₀ b₁ b₂ : I → ℝ)
    (ha₀ : ∀ g, a₀ g ≠ 0) (ha₁ : ∀ g, a₁ g ≠ 0)
    (hb₀ : ∀ i, b₀ i ≠ 0) (hb₁ : ∀ i, b₁ i ≠ 0) (i j : I) :
    lineUnaryRemoval line a₀ a₁ a₂ b₀ b₁ b₂ i j =
      ((∏ g, a₀ g) * ∏ k, b₀ k) *
        ((a₁ (line i) / a₀ (line i)) * (b₁ i / b₀ i)) *
        ((a₁ (line j) / a₀ (line j)) * (b₁ j / b₀ j)) *
        (if line i = line j then a₀ (line i) * a₂ (line i) / (a₁ (line i)) ^ 2 else 1) *
        (if i = j then b₀ i * b₂ i / (b₁ i) ^ 2 else 1) := by
  rw [lineUnaryRemoval, productTwoUpdates_factor a₀ a₁ a₂ ha₀ ha₁,
    productTwoUpdates_factor b₀ b₁ b₂ hb₀ hb₁]
  ring

omit [Fintype I] [Fintype G] in
private theorem normalized_line_unary_correction (line : I → G) (W : ℝ)
    (α : I → ℝ) (γ : G → ℝ) (δ : I → ℝ) :
    (fun i j => W * α i * α j * (if line i = line j then γ (line i) else 1) *
      (if i = j then δ i else 1)) =
    weightedCorrection (twoLevelKernel line (fun _ => false) γ (fun _ => 1)) W α
      (fun i => W * α i ^ 2 * γ (line i) * (1 - δ i)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [weightedCorrection, scaledMatrix, twoLevelKernel, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, ite_true,
      Bool.false_eq_true, false_and, ite_false, mul_one]
    ring
  · by_cases hline : line i = line j <;>
      simp [weightedCorrection, scaledMatrix, twoLevelKernel, hij, hline] <;> ring

/-- The actual line/unary two-removal matrix has the required signature
when each factor satisfies its scalar log-concavity inequality. -/
theorem lineUnaryRemoval_onePositive (line : I → G)
    (a₀ a₁ a₂ : G → ℝ) (b₀ b₁ b₂ : I → ℝ)
    (ha₀ : ∀ g, 0 < a₀ g) (ha₁ : ∀ g, 0 < a₁ g) (ha₂ : ∀ g, 0 ≤ a₂ g)
    (hb₀ : ∀ i, 0 < b₀ i) (hb₁ : ∀ i, 0 < b₁ i)
    (halc : ∀ g, a₀ g * a₂ g ≤ (a₁ g) ^ 2)
    (hblc : ∀ i, b₀ i * b₂ i ≤ (b₁ i) ^ 2) :
    OnePositiveDirection (lineUnaryRemoval line a₀ a₁ a₂ b₀ b₁ b₂).toBilin' := by
  let W := (∏ g, a₀ g) * ∏ i, b₀ i
  let α : I → ℝ := fun i => (a₁ (line i) / a₀ (line i)) * (b₁ i / b₀ i)
  let γ : G → ℝ := fun g => a₀ g * a₂ g / (a₁ g) ^ 2
  let δ : I → ℝ := fun i => b₀ i * b₂ i / (b₁ i) ^ 2
  let K := twoLevelKernel line (fun _ => false) γ (fun _ => 1)
  let κ : I → ℝ := fun i => W * α i ^ 2 * γ (line i) * (1 - δ i)
  have hW : 0 ≤ W := mul_nonneg
    (Finset.prod_nonneg fun g _ => (ha₀ g).le) (Finset.prod_nonneg fun i _ => (hb₀ i).le)
  have hγ₀ (g : G) : 0 ≤ γ g :=
    div_nonneg (mul_nonneg (ha₀ g).le (ha₂ g)) (sq_nonneg _)
  have hγ₁ (g : G) : γ g ≤ 1 := by
    exact (div_le_one (sq_pos_of_pos (ha₁ g))).mpr (halc g)
  have hδ₁ (i : I) : δ i ≤ 1 := by
    exact (div_le_one (sq_pos_of_pos (hb₁ i))).mpr (hblc i)
  have hκ (i : I) : 0 ≤ κ i :=
    mul_nonneg (mul_nonneg (mul_nonneg hW (sq_nonneg _)) (hγ₀ _))
      (sub_nonneg.mpr (hδ₁ i))
  have heq : lineUnaryRemoval line a₀ a₁ a₂ b₀ b₁ b₂ = weightedCorrection K W α κ := by
    rw [← normalized_line_unary_correction line W α γ δ]
    ext i j
    exact lineUnaryRemoval_factor line a₀ a₁ a₂ b₀ b₁ b₂
      (fun g => ne_of_gt (ha₀ g)) (fun g => ne_of_gt (ha₁ g))
      (fun i => ne_of_gt (hb₀ i)) (fun i => ne_of_gt (hb₁ i)) i j
  rw [heq]
  exact correctedTwoLevel_onePositive line (fun _ => false) γ (fun _ => 1)
    W α κ hγ₀ hγ₁ (fun _ => le_refl _) hW hκ

end LineUnary

end ContingencyTables

end OAI
