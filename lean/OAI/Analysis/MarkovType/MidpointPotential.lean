import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

private theorem nonpos_on_unit_interval_of_midpoint
    (g : ℝ → ℝ)
    (hmid : ∀ s t, g ((s + t) / 2) ≤ (g s + g t) / 2)
    (hzero : g 0 ≤ 0) (hone : g 1 ≤ 0)
    (M : ℝ) (hbound : ∀ t, 0 ≤ t → t ≤ 1 → g t ≤ M)
    (t : ℝ) (htzero : 0 ≤ t) (htone : t ≤ 1) : g t ≤ 0 := by
  by_contra h
  have hpos : 0 < g t := lt_of_not_ge h
  have hstep (s : ℝ) (hszero : 0 ≤ s) (hsone : s ≤ 1) :
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 2 * g s ≤ g u := by
    by_cases hs : s ≤ 1 / 2
    · have hm := hmid 0 (2 * s)
      have he : (0 + 2 * s) / 2 = s := by ring
      rw [he] at hm
      refine ⟨2 * s, by linarith, by linarith, ?_⟩
      linarith only [hm, hzero]
    · have hm := hmid (2 * s - 1) 1
      have he : (2 * s - 1 + 1) / 2 = s := by ring
      rw [he] at hm
      refine ⟨2 * s - 1, by linarith, by linarith, ?_⟩
      linarith only [hm, hone]
  have hgrowth (n : ℕ) :
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (n : ℝ) * g t + g t ≤ g s := by
    induction n with
    | zero => exact ⟨t, htzero, htone, by simp⟩
    | succ n ih =>
        obtain ⟨s, hs0, hs1, hvalue⟩ := ih
        obtain ⟨u, hu0, hu1, hdouble⟩ := hstep s hs0 hs1
        have hn : 0 ≤ (n : ℝ) * g t := mul_nonneg (Nat.cast_nonneg n) hpos.le
        refine ⟨u, hu0, hu1, ?_⟩
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith only [hn, hvalue, hdouble]
  obtain ⟨n, hn⟩ := exists_nat_gt (M / g t)
  have hlarge : M < (n : ℝ) * g t := (div_lt_iff₀ hpos).mp hn
  obtain ⟨s, hs0, hs1, hvalue⟩ := hgrowth n
  have hsmall := hbound s hs0 hs1
  linarith only [hlarge, hsmall, hvalue, hpos]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_of_midpoint_norm_power_bound
    (q : ℝ) (hq : 0 ≤ q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hbound : ∀ x, F x ≤ ‖x‖ ^ q)
    (hmid : ∀ x y, F ((2 : ℝ)⁻¹ • (x + y)) ≤ (F x + F y) / 2) :
    ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let g : ℝ → ℝ := fun t =>
    F ((1 - t) • x + t • y) - ((1 - t) * F x + t * F y)
  have hgmid (s t : ℝ) : g ((s + t) / 2) ≤ (g s + g t) / 2 := by
    have he : (2 : ℝ)⁻¹ •
        (((1 - s) • x + s • y) + ((1 - t) • x + t • y)) =
        (1 - (s + t) / 2) • x + ((s + t) / 2) • y := by module
    have hm := hmid ((1 - s) • x + s • y) ((1 - t) • x + t • y)
    rw [he] at hm
    dsimp [g]
    nlinarith only [hm]
  have hgzero : g 0 ≤ 0 := by simp [g]
  have hgone : g 1 ≤ 0 := by simp [g]
  have hgBound (t : ℝ) (htzero : 0 ≤ t) (htone : t ≤ 1) :
      g t ≤ (‖x‖ + ‖y‖) ^ q := by
    have hleft : 0 ≤ 1 - t := sub_nonneg.mpr htone
    have hnorm : ‖(1 - t) • x + t • y‖ ≤ ‖x‖ + ‖y‖ := by
      calc
        ‖(1 - t) • x + t • y‖ ≤ ‖(1 - t) • x‖ + ‖t • y‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖y‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hleft,
            abs_of_nonneg htzero]
        _ ≤ ‖x‖ + ‖y‖ := add_le_add
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 htzero) (norm_nonneg x))
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right htone (norm_nonneg y))
    have hupper := (hbound ((1 - t) • x + t • y)).trans
      (Real.rpow_le_rpow (norm_nonneg _) hnorm hq)
    have hlinear : 0 ≤ (1 - t) * F x + t * F y :=
      add_nonneg (mul_nonneg hleft (hF x)) (mul_nonneg htzero (hF y))
    dsimp [g]
    linarith only [hupper, hlinear]
  have hbone : b ≤ 1 := by linarith only [ha, hab]
  have hvalue := nonpos_on_unit_interval_of_midpoint g hgmid hgzero hgone
    ((‖x‖ + ‖y‖) ^ q) hgBound b hb hbone
  have hae : a = 1 - b := by linarith only [hab]
  rw [hae]
  change F ((1 - b) • x + b • y) ≤ (1 - b) * F x + b * F y
  exact sub_nonpos.mp hvalue

end MarkovSuperreflexivity

end OAI
