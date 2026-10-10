import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Tactic

namespace OAI

/-!
# Scalar estimates for the smooth correction iteration

The scalar recurrence used in `exact-correction.tex`, subsection
"Initialization and passage through the derivative orders", is treated here.
These are estimates for that iteration, not an isometric immersion existence theorem.
-/

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology

/-- A tail of a subsolution is dominated by the corresponding affine recurrence. -/
theorem affine_tail_bound {x : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (N : ℕ)
    (hstep : ∀ n, N ≤ n → x (n + 1) ≤ a * x n + b) (j : ℕ) :
    x (N + j) ≤ arithGeom a b (x N) j := by
  induction j with
  | zero => simp
  | succ j hj =>
    calc
      x (N + (j + 1)) ≤ a * x (N + j) + b := hstep (N + j) (by omega)
      _ ≤ a * arithGeom a b (x N) j + b := by gcongr
      _ = arithGeom a b (x N) (j + 1) := rfl

/-- An affine subsolution with contraction coefficient eventually lies below any
strict upper bound for the fixed point. -/
theorem eventually_lt_of_affine_tail {x : ℕ → ℝ} {a b L : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hL : b / (1 - a) < L) (N : ℕ)
    (hstep : ∀ n, N ≤ n → x (n + 1) ≤ a * x n + b) :
    ∀ᶠ n in atTop, x n < L := by
  have ht : Tendsto (arithGeom a b (x N)) atTop (𝓝 (b / (1 - a))) :=
    tendsto_arithGeom_nhds_of_lt_one ha ha1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hL))
  filter_upwards [eventually_ge_atTop (N + K)] with n hn
  have hNK : N + (n - N) = n := by omega
  have hbound := affine_tail_bound ha N hstep (n - N)
  rw [hNK] at hbound
  exact lt_of_le_of_lt hbound (hK (n - N) (by omega))

/-- The all-order recurrence from the manuscript eventually enters every
strict upper neighborhood of its baseline. No initial bound on `x` is required. -/
theorem eventually_lt_of_vanishing_recurrence {x c : ℕ → ℝ} {A L : ℝ}
    (hx : ∀ n, 0 ≤ x n) (hA : 0 ≤ A)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ n, x (n + 1) ≤ A + c n * (1 + x n)) (hAL : A < L) :
    ∀ᶠ n in atTop, x n < L := by
  let a : ℝ := (L - A) / (2 * (L + 1))
  have hL : 0 < L := lt_of_le_of_lt hA hAL
  have hden : 0 < 2 * (L + 1) := by positivity
  have ha : 0 < a := div_pos (sub_pos.mpr hAL) hden
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hden).mpr
    linarith
  have hafix : (A + a) / (1 - a) < L := by
    apply (div_lt_iff₀ (sub_pos.mpr ha1)).mpr
    have heq : a * (L + 1) = (L - A) / 2 := by
      dsimp [a]
      field_simp
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hc.eventually (gt_mem_nhds ha))
  apply eventually_lt_of_affine_tail ha.le ha1 hafix N
  intro n hn
  calc
    x (n + 1) ≤ A + c n * (1 + x n) := hstep n
    _ ≤ A + a * (1 + x n) := by
      have hn0 : 0 ≤ 1 + x n := by linarith [hx n]
      have hm := mul_le_mul_of_nonneg_right (hN n hn).le hn0
      exact add_le_add_right hm A
    _ = a * x n + (A + a) := by ring

/-- In particular, each fixed derivative order reaches the next block's
budget after finitely many steps, as asserted in the exact-correction proof. -/
theorem eventually_below_budget {x c : ℕ → ℝ} {B : ℝ}
    (hB : 0 < B) (hx : ∀ n, 0 ≤ x n) (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ n, x (n + 1) ≤ B / 4 + c n * (1 + x n)) :
    ∀ᶠ n in atTop, x n < B :=
  eventually_lt_of_vanishing_recurrence hx (by positivity) hc hstep (by linarith)

/-- All six exponents in the exact-correction error table are positive at
and after the initial block `k = 10`. -/
theorem error_exponents_pos {k : ℝ} (hk : 10 ≤ k) :
    0 < (13 * k + 8) / 5 ∧
    0 < (3 * k - 18) / 5 ∧
    0 < (18 * k + 8) / 5 ∧
    0 < (38 * k + 28) / 5 ∧
    0 < (13 * k + 8) / 5 ∧
    0 < (33 * k + 28) / 5 := by
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> linarith

end ClosedSurfaceR4.ExactCorrection

end OAI
