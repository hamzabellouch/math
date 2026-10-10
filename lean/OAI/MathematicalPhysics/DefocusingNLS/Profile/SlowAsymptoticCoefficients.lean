import OAI.MathematicalPhysics.DefocusingNLS.Profile.CompactifiedSlowSmoothness
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace OAI

/-! # Explicit Pochhammer coefficients of the outgoing expansion -/

open Polynomial

namespace DefocusingNLS

theorem slowAsymptoticJet_eq_pochhammer (q : ℂ) (m n : ℕ) :
    slowAsymptoticJet q m n =
      (ascPochhammer ℂ n).eval q *
        (descPochhammer ℂ n).eval ((m : ℂ) - 1 - q) := by
  induction n generalizing q with
  | zero => simp [slowAsymptoticJet]
  | succ n ih =>
      rw [slowAsymptoticJet, ih, ascPochhammer_succ_left, descPochhammer_succ_left]
      simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one, eval_sub]
      have he : (m : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q - 1 := by ring
      rw [he]
      ring

end DefocusingNLS

end OAI
