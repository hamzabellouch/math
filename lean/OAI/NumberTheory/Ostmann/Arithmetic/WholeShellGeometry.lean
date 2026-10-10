import OAI.NumberTheory.Ostmann.Construction.WholePrimeGrid

namespace OAI

/-! # Exact interval geometry for the full original bulk prime shell -/

namespace Ostmann
open scoped Classical

noncomputable def wholeShellLower (a b : ℝ) (c : Fin (wholePrimeGridCount b)) : ℝ :=
  Real.exp a + (c : ℝ) * ((Real.exp b - Real.exp a) / (wholePrimeGridCount b : ℝ))

noncomputable def wholeShellUpper (a b : ℝ) (c : Fin (wholePrimeGridCount b)) : ℝ :=
  Real.exp a + ((c : ℝ) + 1) * ((Real.exp b - Real.exp a) / (wholePrimeGridCount b : ℝ))

theorem whole_shell_geometry (a b : ℝ) (hab : a ≤ b) :
    (∀ c, Real.exp a ≤ wholeShellLower a b c) ∧
    (∀ c, wholeShellLower a b c ≤ wholeShellUpper a b c) ∧
    (∀ c, wholeShellUpper a b c ≤ wholeShellLower a b c + 1) ∧
    (∀ c d, c ≠ d → wholeShellUpper a b c ≤ wholeShellLower a b d ∨
      wholeShellUpper a b d ≤ wholeShellLower a b c) := by
  have hwidth : Real.exp b - Real.exp a ≤ (wholePrimeGridCount b : ℝ) := by
    have hc := Nat.le_ceil (Real.exp (b + 1))
    have he : Real.exp b ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr (by linarith)
    unfold wholePrimeGridCount
    push_cast
    linarith [Real.exp_pos a]
  have hh := interval_grid_width (wholePrimeGridCount_pos b)
    (Real.exp_le_exp.mpr hab) hwidth
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only [wholeShellLower]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hh.1)
  · intro c
    dsimp only [wholeShellLower, wholeShellUpper]
    nlinarith [hh.1]
  · intro c
    dsimp only [wholeShellLower, wholeShellUpper]
    nlinarith [hh.2.1]
  · intro c d hcd
    rcases lt_or_gt_of_ne hcd with hlt | hgt
    · left
      have h : (c : ℝ) + 1 ≤ d := by
        exact_mod_cast (show c.val + 1 ≤ d.val from hlt)
      dsimp only [wholeShellLower, wholeShellUpper]
      nlinarith [hh.1]
    · right
      have h : (d : ℝ) + 1 ≤ c := by
        exact_mod_cast (show d.val + 1 ≤ c.val from hgt)
      dsimp only [wholeShellLower, wholeShellUpper]
      nlinarith [hh.1]

theorem whole_shell_support (q : ℕ) [NeZero q] (a b : ℝ) (hab : a ≤ b)
    (hq : (q : ℝ) ≤ Real.exp (Real.exp a)) :
    primeCellSupport q (fun c : Fin (wholePrimeGridCount b) × (ZMod q)ˣ => c.2.val.val)
      (fun c => wholeShellLower a b c.1) (fun c => wholeShellUpper a b c.1) =
      primeLogCellSet 1 0 (Real.exp a) (Real.exp b) := by
  exact whole_interval_prime_grid_support q a b hab hq

end Ostmann

end OAI
