import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.HyperbolaCorrelation

/-- The common support of two columns cut off by a product bound. -/
theorem product_support_iff (X m n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂) :
    (m * n₁ ≤ X ∧ m * n₂ ≤ X) ↔ m ≤ X / max n₁ n₂ := by
  rw [Nat.le_div_iff_mul_le hn, mul_max, max_le_iff]

/-- Intersecting two hyperbolic columns leaves an ordinary integer interval.
Empty intervals and a zero value of one of the two column indices are allowed. -/
theorem filter_common_support (X L U n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂) :
    (Finset.Icc L U).filter (fun m => m * n₁ ≤ X ∧ m * n₂ ≤ X) =
      Finset.Icc L (min U (X / max n₁ n₂)) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, product_support_iff X m n₁ n₂ hn,
    le_min_iff]
  tauto

/-- Exact correlation identity for arbitrary complex hyperbolic columns. -/
theorem cutoff_correlation (X L U n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂)
    (f g : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc L U,
      (if m * n₁ ≤ X then f m else 0) *
        conj (if m * n₂ ≤ X then g m else 0)) =
      ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)), f m * conj (g m) := by
  rw [← filter_common_support X L U n₁ n₂ hn, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h₁ : m * n₁ ≤ X <;> by_cases h₂ : m * n₂ ≤ X <;> simp [h₁, h₂]

/-- The standard real-frequency complex phase. -/
def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_sub (x y : ℝ) : phase (x - y) = phase x * conj (phase y) := by
  simp only [phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- A column of a bilinear exponential sum with its actual hyperbolic support. -/
def column (α : ℝ) (X n m : ℕ) : ℂ :=
  if m * n ≤ X then phase (α * (m : ℝ) * (n : ℝ)) else 0

/-- The off-diagonal correlation is a geometric exponential sum on one interval,
not a sum over an arbitrary subset. Differences are taken in `ℝ`, so negative
frequencies are retained rather than truncated by natural subtraction. -/
theorem column_correlation (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) :
    (∑ m ∈ Finset.Icc L U, column α X n₁ m * conj (column α X n₂ m)) =
      ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)),
        phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  unfold column
  rw [cutoff_correlation X L U n₁ n₂ hn]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← phase_sub]
  congr 1
  ring

/-- Diagonal correlations count the surviving rows exactly. -/
theorem column_diagonal (α : ℝ) (X L U n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc L U, column α X n m * conj (column α X n m)) =
      ((Finset.Icc L (min U (X / n))).card : ℂ) := by
  rw [column_correlation α X L U n n (by simpa using hn)]
  simp [phase]

/-- Unit modulus survives restriction, the hypothesis used in finite Type-II
Cauchy--Schwarz estimates. -/
theorem norm_column_le_one (α : ℝ) (X n m : ℕ) : ‖column α X n m‖ ≤ 1 := by
  unfold column
  split_ifs <;> simp

/-- Constant column weights factor out before the geometric estimate. -/
theorem weighted_column_correlation (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) (b₁ b₂ : ℂ) :
    (∑ m ∈ Finset.Icc L U,
      (b₁ * column α X n₁ m) * conj (b₂ * column α X n₂ m)) =
      (b₁ * conj b₂) *
        ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)),
          phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  rw [← column_correlation α X L U n₁ n₂ hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul]
  ring

/-- The weighted-correlation norm has precisely the product of the two weights. -/
theorem norm_weighted_column_correlation (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) (b₁ b₂ : ℂ) :
    ‖∑ m ∈ Finset.Icc L U,
      (b₁ * column α X n₁ m) * conj (b₂ * column α X n₂ m)‖ =
      ‖b₁‖ * ‖b₂‖ *
        ‖∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)),
          phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ)))‖ := by
  rw [weighted_column_correlation α X L U n₁ n₂ hn b₁ b₂]
  simp only [norm_mul, Complex.norm_conj]

end Problem337.HyperbolaCorrelation

end

end OAI
