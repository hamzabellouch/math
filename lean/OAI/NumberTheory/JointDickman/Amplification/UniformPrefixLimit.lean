import OAI.NumberTheory.JointDickman.Amplification.UniformPrefixGrid

namespace OAI

/-! # A uniform scaled-prefix consequence of marginal mean convergence -/
namespace JointDickman
open Finset Filter
open scoped Topology

/-- Pointwise convergence at every fixed positive counting multiple becomes
uniform on a bounded interval because each summand is bounded. -/
theorem uniform_prefix_of_marginal_means (f : ℝ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x n, ‖f x n‖ ≤ C)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊A * x⌋₊, f x n) / (x : ℂ)) atTop (𝓝 0))
    (R : ℝ) (_hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (0 : ℝ) (R * x),
      ‖∑ n ∈ Ioc 0 ⌊u⌋₊, f x n‖ ≤ ε * x := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (4 * C / ε))
  have hm1 : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmpos : 0 < m := by exact_mod_cast hm0
  have hCm : C / (m : ℝ) ≤ ε / 4 := by
    apply (div_le_iff₀ hm0).mpr
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hm)
    nlinarith
  let N := ⌈R * (m : ℝ)⌉₊
  have hgrid (j : ℕ) : ∀ᶠ x : ℝ in atTop,
      ‖∑ n ∈ Ioc 0 ⌊((j : ℝ) / m) * x⌋₊, f x n‖ ≤ (ε / 2) * x := by
    by_cases hj : j = 0
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [hj, Nat.cast_zero, zero_div, zero_mul, Nat.floor_zero, Ioc_self, sum_empty, norm_zero]
      exact mul_nonneg (by positivity) hx
    · have hjr : 0 < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
      have hh := ((hmean ((j : ℝ) / m) (div_pos hjr hm0)).norm).eventually
        (gt_mem_nhds (show ‖(0 : ℂ)‖ < ε / 2 by simpa using (show 0 < ε / 2 by positivity)))
      filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hx
      exact ((div_lt_iff₀ hx0).mp hx).le
  have hall : ∀ᶠ x : ℝ in atTop, ∀ j ∈ range (N + 1),
      ‖∑ n ∈ Ioc 0 ⌊((j : ℝ) / m) * x⌋₊, f x n‖ ≤ (ε / 2) * x :=
    (eventually_all_finset (range (N + 1))).mpr (fun j _ => hgrid j)
  filter_upwards [hall, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (4 * C / ε)]
    with x hx hx0 hxlarge
  intro u hu
  have hcover : R * x ≤ (N : ℝ) * (x / m) := by
    have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (R * (m : ℝ)))
      (show 0 ≤ x / m by positivity)
    change R * (m : ℝ) * (x / m) ≤ (N : ℝ) * (x / m) at hh
    simpa only [mul_assoc, mul_div_cancel₀ _ hm0.ne'] using hh
  have hmesh := prefix_grid_uniform_bound (f x) N hC (hf x) (div_pos hx0 hm0)
    (fun j hj => by
      have hh := hx j (mem_range.mpr (by omega))
      have he : (j : ℝ) * (x / m) = ((j : ℝ) / m) * x := by ring
      simpa only [he] using hh)
    (show u ∈ Set.Icc (0 : ℝ) ((N : ℝ) * (x / m)) from ⟨hu.1, hu.2.trans hcover⟩)
  have hCsmall : C ≤ (ε / 4) * x := by
    have hh := (div_le_iff₀ hε).mp hxlarge
    nlinarith
  have hCmesh : C * (x / m) ≤ (ε / 4) * x := by
    have hh := mul_le_mul_of_nonneg_right hCm hx0.le
    convert hh using 1
    ring
  nlinarith

end JointDickman

end OAI
