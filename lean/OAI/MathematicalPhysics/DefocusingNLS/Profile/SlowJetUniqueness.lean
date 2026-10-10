import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowHigherDerivatives
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Convex

namespace OAI

/-! # Nonvanishing of the slow-solution jet

The differential equation determines all higher derivatives from the first
two. Analytic uniqueness and the proved leading asymptotic exclude a common
zero of the value and first derivative.
-/

open Filter Topology Set

namespace DefocusingNLS

theorem hasDerivAt_iteratedDeriv_slow (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : x ∈ Complex.slitPlane) :
    HasDerivAt (iteratedDeriv n (regularizedSlowSolution q m))
      (iteratedDeriv (n + 1) (regularizedSlowSolution q m) x) x := by
  have ha := (analyticOnNhd_regularizedSlowSolution_slit q m hq).iterated_deriv n x hx
  rw [← iteratedDeriv_eq_iterate] at ha
  simpa only [iteratedDeriv_succ] using ha.differentiableAt.hasDerivAt

theorem slow_higher_ode (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    x * iteratedDeriv (n + 2) (regularizedSlowSolution q m) x +
      ((m : ℂ) + n - x) * iteratedDeriv (n + 1) (regularizedSlowSolution q m) x -
      (q + n) * iteratedDeriv n (regularizedSlowSolution q m) x = 0 := by
  induction n generalizing x with
  | zero =>
      simpa only [Nat.cast_zero, add_zero, iteratedDeriv_succ, iteratedDeriv_zero] using
        regularizedSlowSolution_kummer_equation q m x hq hx
  | succ n ih =>
      let H := regularizedSlowSolution q m
      have hd (k : ℕ) := hasDerivAt_iteratedDeriv_slow k q m x hq
        (Complex.mem_slitPlane_iff.mpr (Or.inl hx))
      have hF := (((hasDerivAt_id x).fun_mul (hd (n + 2))).add
        (((hasDerivAt_const x ((m : ℂ) + n)).sub (hasDerivAt_id x)).fun_mul
          (hd (n + 1)))).sub ((hd n).const_mul (q + n))
      have he : (fun z => z * iteratedDeriv (n + 2) H z +
          ((m : ℂ) + n - z) * iteratedDeriv (n + 1) H z -
          (q + n) * iteratedDeriv n H z) =ᶠ[𝓝 x] (fun _ => 0) := by
        have hu : {z : ℂ | 0 < z.re} ∈ 𝓝 x :=
          (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
        filter_upwards [hu] with z hz
        exact ih z hz
      have hz := (hF.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const x (0 : ℂ))
      simp only [one_mul, zero_sub, neg_mul, Pi.sub_apply, id_eq] at hz
      change x * iteratedDeriv (n + 1 + 2) H x +
        ((m : ℂ) + (n + 1 : ℕ) - x) * iteratedDeriv (n + 1 + 1) H x -
        (q + (n + 1 : ℕ)) * iteratedDeriv (n + 1) H x = 0
      push_cast
      simp only [show n + 1 + 2 = n + 2 + 1 by omega,
        show n + 1 + 1 = n + 2 by omega] at *
      linear_combination hz

theorem slow_higher_ode_closed (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    x * iteratedDeriv (n + 2) (regularizedSlowSolution q m) x +
      ((m : ℂ) + n - x) * iteratedDeriv (n + 1) (regularizedSlowSolution q m) x -
      (q + n) * iteratedDeriv n (regularizedSlowSolution q m) x = 0 := by
  rcases hx.eq_or_lt with hx | hx
  · have him : x.im ≠ 0 := by
      intro h
      exact hx0 (Complex.ext hx.symm h)
    have hslit := Complex.mem_slitPlane_iff.mpr (Or.inr him)
    have hc (k : ℕ) : ContinuousAt (iteratedDeriv k (regularizedSlowSolution q m)) x :=
      (hasDerivAt_iteratedDeriv_slow k q m x hq hslit).continuousAt
    apply eq_zero_on_imaginary_boundary hx.symm
    · exact ((continuousAt_id.mul (hc (n + 2))).add
        ((continuousAt_const.sub continuousAt_id).mul (hc (n + 1)))).sub
        (continuousAt_const.mul (hc n))
    · intro z hz
      exact slow_higher_ode n q m z hq hz
  · exact slow_higher_ode n q m x hq hx

theorem regularizedSlowSolution_jet_nonzero (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    regularizedSlowSolution q m x ≠ 0 ∨ deriv (regularizedSlowSolution q m) x ≠ 0 := by
  by_contra h
  push Not at h
  have hd : ∀ n, iteratedDeriv n (regularizedSlowSolution q m) x = 0 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact h.1
    | one => simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h.2
    | more n hn hn1 =>
        have he := slow_higher_ode_closed n q m x hq hx hx0
        rw [hn, hn1, mul_zero, mul_zero, add_zero, sub_zero] at he
        exact (mul_eq_zero.mp he).resolve_left hx0
  have hslit : x ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with hx | hx
    · right
      intro him
      exact hx0 (Complex.ext hx.symm him)
    · exact Or.inl hx
  have ha := analyticOnNhd_regularizedSlowSolution_slit q m hq
  have htop : analyticOrderAt (regularizedSlowSolution q m) x = ⊤ := by
    apply ENat.eq_top_iff_forall_ge.mpr
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha x hslit)).mpr
      (fun i _ => hd i)
  have he := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (Complex.starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected
    hslit (analyticOrderAt_eq_top.mp htop)
  obtain ⟨R, hR, hnonzero⟩ := regularizedSlowSolution_nonzero_at_large_norm q m hq
  have hr : 0 < R + 1 := by linarith
  have hzero := he (Complex.ofReal_mem_slitPlane.mpr hr)
  exact hnonzero _ (by simpa using hr.le)
    (by rw [Complex.norm_of_nonneg hr.le]; linarith) hzero

end DefocusingNLS

end OAI
