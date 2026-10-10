import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAsymptoticBound
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace OAI

/-! # Successive derivatives and the Pochhammer normalization -/

open Filter Topology Polynomial

namespace DefocusingNLS

theorem iteratedDeriv_regularizedSlowSolution (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    iteratedDeriv n (regularizedSlowSolution q m) x =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q *
        regularizedSlowSolution (q + n) (m + n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hq' : -1 < (q + n).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hd := (hasDerivAt_regularizedSlowSolution_shift (q + n) (m + n) x hq' hx).const_mul
      ((-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q)
    have he : iteratedDeriv n (regularizedSlowSolution q m) =ᶠ[𝓝 x]
        (fun y => (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q *
          regularizedSlowSolution (q + n) (m + n) y) := by
      have hs : {y : ℂ | 0 < y.re} ∈ 𝓝 x :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
      filter_upwards [hs] with y hy
      exact ih y hy
    rw [iteratedDeriv_succ, (hd.congr_of_eventuallyEq he).deriv,
      ascPochhammer_succ_eval, pow_succ]
    have heq : q + (n + 1 : ℕ) = q + n + 1 := by push_cast; ring
    rw [heq, Nat.add_assoc]
    ring

theorem iteratedDeriv_regularizedSlowSolution_closed (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    iteratedDeriv n (regularizedSlowSolution q m) x =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q *
        regularizedSlowSolution (q + n) (m + n) x := by
  rcases hx.eq_or_lt with hx | hx
  · have him : x.im ≠ 0 := by
      intro hi
      apply hx0
      exact Complex.ext hx.symm hi
    have hslit : x ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr him)
    have hq' : -1 < (q + n).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have ha := analyticOnNhd_regularizedSlowSolution_slit q m hq
    have hb := analyticOnNhd_regularizedSlowSolution_slit (q + n) (m + n) hq'
    have hc : ContinuousAt (iteratedDeriv n (regularizedSlowSolution q m)) x := by
      rw [iteratedDeriv_eq_iterate]
      exact (ha.iterated_deriv n x hslit).continuousAt
    have he : iteratedDeriv n (regularizedSlowSolution q m) x -
        (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval q *
          regularizedSlowSolution (q + n) (m + n) x = 0 := by
      apply eq_zero_on_imaginary_boundary hx.symm
      · exact hc.sub (continuousAt_const.mul (hb x hslit).continuousAt)
      · intro y hy
        rw [iteratedDeriv_regularizedSlowSolution n q m y hq hy, sub_self]
    exact sub_eq_zero.mp he
  · exact iteratedDeriv_regularizedSlowSolution n q m x hq hx

end DefocusingNLS

end OAI
