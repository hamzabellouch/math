import OAI.Probability.SpanningForest.SchauderTents

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.DyadicInterpolation

open SchauderTents

def grid (n j : ℕ) : ℝ := (j : ℝ) / 2 ^ n

@[simp] theorem grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]
@[simp] theorem grid_zero_level (j : ℕ) : grid 0 j = j := by simp [grid]

theorem grid_succ_even (n j : ℕ) : grid (n + 1) (2 * j) = grid n j := by
  unfold grid
  push_cast
  rw [pow_succ]
  field_simp

theorem grid_succ_odd (n j : ℕ) : grid (n + 1) (2 * j + 1) = midpoint n j := by
  unfold grid SchauderTents.midpoint
  push_cast
  rw [pow_succ]
  field_simp

theorem midpoint_eq_average (n j : ℕ) :
    midpoint n j = (grid n j + grid n (j + 1)) / 2 := by
  unfold SchauderTents.midpoint grid
  push_cast
  ring

def residual (x : ℝ → ℝ) (n k : ℕ) : ℝ :=
  x (midpoint n k) - (x (grid n k) + x (grid n (k + 1))) / 2

def coefficient (x : ℝ → ℝ) (n k : ℕ) : ℝ :=
  2 * residual x n k / amplitude n

def approx (x : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  x 0 + (x 1 - x 0) * t + ∑ m ∈ Finset.range n, level m (coefficient x m) t

theorem continuous_approx (x : ℝ → ℝ) (n : ℕ) : Continuous (approx x n) := by
  unfold approx
  apply Continuous.add
  · fun_prop
  · exact continuous_finsetSum _ fun m _ => continuous_level m (coefficient x m)

theorem approx_succ (x : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    approx x (n + 1) t = approx x n t + level n (coefficient x n) t := by
  simp only [approx, Finset.sum_range_succ]
  ring

theorem approx_old_midpoint (x : ℝ → ℝ) (n j : ℕ) :
    approx x n (midpoint n j) =
      (approx x n (grid n j) + approx x n (grid n (j + 1))) / 2 := by
  have hs :
      (∑ m ∈ Finset.range n, level m (coefficient x m) (midpoint n j)) =
      ((∑ m ∈ Finset.range n, level m (coefficient x m) (grid n j)) +
        ∑ m ∈ Finset.range n, level m (coefficient x m) (grid n (j + 1))) / 2 := by
    calc
      _ = ∑ m ∈ Finset.range n,
          (level m (coefficient x m) (grid n j) +
            level m (coefficient x m) (grid n (j + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        simpa only [grid, Nat.cast_add, Nat.cast_one] using
          level_old_midpoint (Finset.mem_range.mp hm) (coefficient x m) j
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp only [approx]
  rw [hs, midpoint_eq_average]
  ring

theorem level_coefficient_midpoint (x : ℝ → ℝ) (n k : ℕ) (hk : k < 2 ^ n) :
    level n (coefficient x n) (midpoint n k) = residual x n k := by
  rw [level_at_midpoint n k _ hk, coefficient]
  have ha : amplitude n ≠ 0 := ne_of_gt (amplitude_pos n)
  field_simp

theorem approx_grid (x : ℝ → ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n) :
    approx x n (grid n j) = x (grid n j) := by
  induction n generalizing j with
  | zero =>
      have hj' : j = 0 ∨ j = 1 := by norm_num at hj; omega
      rcases hj' with rfl | rfl <;> simp [approx, grid]
  | succ n ih =>
      obtain ⟨k, h | h⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 :=
        ⟨j / 2, by omega⟩
      · subst j
        have hk : k ≤ 2 ^ n := by rw [pow_succ] at hj; omega
        rw [grid_succ_even, approx_succ]
        have hz : level n (coefficient x n) (grid n k) = 0 := by
          simpa only [Nat.add_zero, grid] using
            level_prior_grid_zero n 0 k (coefficient x n)
        rw [hz, add_zero, ih k hk]
      · subst j
        have hk : k < 2 ^ n := by rw [pow_succ] at hj; omega
        rw [grid_succ_odd, approx_succ, approx_old_midpoint,
          level_coefficient_midpoint x n k hk, ih k hk.le, ih (k + 1) (by omega)]
        unfold residual
        ring

theorem abs_residual_le (x : ℝ → ℝ) (n k : ℕ) {D : ℝ}
    (hleft : |x (midpoint n k) - x (grid n k)| ≤ D)
    (hright : |x (grid n (k + 1)) - x (midpoint n k)| ≤ D) :
    |residual x n k| ≤ D := by
  obtain ⟨hl₁, hl₂⟩ := abs_le.mp hleft
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hright
  rw [residual, abs_le]
  constructor <;> linarith

theorem abs_residual_le_of_increments (x : ℝ → ℝ) (n k : ℕ) {D : ℝ}
    (hk : k < 2 ^ n)
    (hinc : ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ D) :
    |residual x n k| ≤ D := by
  apply abs_residual_le
  · have h := hinc (2 * k) (by rw [pow_succ]; omega)
    simpa only [grid_succ_even, grid_succ_odd] using h
  · have h := hinc (2 * k + 1) (by rw [pow_succ]; omega)
    have heq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    simpa only [heq, grid_succ_even, grid_succ_odd] using h

theorem abs_approx_succ_sub_le_of_residual (x : ℝ → ℝ) (n : ℕ) {D : ℝ}
    (hD : 0 ≤ D) (hres : ∀ k < 2 ^ n, |residual x n k| ≤ D) (t : ℝ) :
    |approx x (n + 1) t - approx x n t| ≤ D := by
  have ha : 0 < amplitude n := amplitude_pos n
  have hC : 0 ≤ 2 * D / amplitude n := div_nonneg (by positivity) ha.le
  have hc : ∀ k < 2 ^ n, |coefficient x n k| ≤ 2 * D / amplitude n := by
    intro k hk
    rw [coefficient, abs_div, abs_mul, abs_of_pos ha,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hres k hk) (by norm_num)) ha.le
  have h := abs_level_le n (coefficient x n) hC hc t
  have hbound : (2 * D / amplitude n) * amplitude n / 2 = D := by
    field_simp
  rw [hbound] at h
  simpa only [approx_succ, add_sub_cancel_left] using h

theorem abs_approx_succ_sub_le (x : ℝ → ℝ) (n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hinc : ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ D) (t : ℝ) :
    |approx x (n + 1) t - approx x n t| ≤ D :=
  abs_approx_succ_sub_le_of_residual x n hD
    (fun k hk => abs_residual_le_of_increments x n k hk hinc) t

variable {Ω : Type*} [MeasurableSpace Ω] (x : Ω → ℝ → ℝ)
    (hx : ∀ t, Measurable (fun ω => x ω t))

include hx

theorem measurable_residual (n k : ℕ) :
    Measurable (fun ω => residual (x ω) n k) := by
  exact (hx _).sub (((hx _).add (hx _)).div_const 2)

theorem measurable_coefficient (n k : ℕ) :
    Measurable (fun ω => coefficient (x ω) n k) := by
  exact ((measurable_residual x hx n k).const_mul 2).div_const _

theorem measurable_approx (n : ℕ) :
    Measurable (fun q : Ω × ℝ => approx (x q.1) n q.2) := by
  unfold approx level
  apply Measurable.add
  · exact ((hx 0).comp measurable_fst).add
      ((((hx 1).sub (hx 0)).comp measurable_fst).mul measurable_snd)
  · apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro k hk
    exact ((measurable_coefficient x hx m k).comp measurable_fst).mul
      ((continuous_tent m k).measurable.comp measurable_snd)

end Problem336.DyadicInterpolation

end

end OAI
