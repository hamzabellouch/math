import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupport

namespace OAI

/-! # Size and separation on the support of the smooth giant law -/

namespace Ostmann

theorem smoothGiantPrior_active_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : smoothGiantPrior P φ G p ≠ 0) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) := by
  have hφ : φ (Real.log (p : ℕ) - G) ≠ 0 := by
    intro h
    apply hp
    simp only [smoothGiantPrior, h, mul_zero, zero_div]
  have habs : |Real.log (p : ℕ) - G| < 1 := lt_of_not_ge (fun h => hφ (hout _ h))
  have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP _ p.property).pos
  constructor
  · apply (Real.exp_lt_exp.mpr (show G - 1 < Real.log (p : ℕ) by linarith [(abs_lt.mp habs).1])).trans_eq
    exact Real.exp_log hpos
  · rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr (by linarith [(abs_lt.mp habs).2])

theorem smoothGiantPrior_active_separation (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (N : ℕ) (hN : (N : ℝ) ≤ Real.exp (G - 1))
    (hQ : ∀ q : Q, (q : ℝ) ≤ Real.exp (G - 1)) :
    (∀ p : P, smoothGiantPrior P φ G p ≠ 0 → N < (p : ℕ)) ∧
      (∀ p : P, smoothGiantPrior P φ G p ≠ 0 → ∀ q : Q, (p : ℕ) ≠ (q : ℕ)) := by
  constructor
  · intro p hp
    exact_mod_cast hN.trans_lt (smoothGiantPrior_active_bounds P hP φ G hout p hp).1
  · intro p hp q heq
    have hb := (hQ q).trans_lt (smoothGiantPrior_active_bounds P hP φ G hout p hp).1
    exact (ne_of_lt hb) (by exact_mod_cast heq.symm)

end Ostmann

end OAI
