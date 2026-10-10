import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowEulerEquation

namespace OAI

/-! # Kummer's differential equation for the Euler integral

The Euler integral satisfies the equation on its initial complex half-planes.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

noncomputable def slowEulerIntegral (q : ℂ) (m : ℕ) (x : ℂ) : ℂ :=
  ∫ v : ℝ in Set.Ioi 0, slowEulerKernel q m x v

theorem hasDerivAt_slowEulerIntegral (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (slowEulerIntegral q m) (-slowEulerIntegral (q + 1) (m + 1) x) x :=
  hasDerivAt_integral_slowEulerKernel q m x hq hx

theorem deriv_slowEulerIntegral (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    deriv (slowEulerIntegral q m) x = -slowEulerIntegral (q + 1) (m + 1) x :=
  (hasDerivAt_slowEulerIntegral q m x hq hx).deriv

theorem hasDerivAt_deriv_slowEulerIntegral (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (deriv (slowEulerIntegral q m))
      (slowEulerIntegral (q + 2) (m + 2) x) x := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have h := (hasDerivAt_slowEulerIntegral (q + 1) (m + 1) x hq' hx).neg
  have heq : deriv (slowEulerIntegral q m) =ᶠ[𝓝 x]
      (fun z => -slowEulerIntegral (q + 1) (m + 1) z) := by
    have hs : {z : ℂ | 0 < z.re} ∈ 𝓝 x :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
    filter_upwards [hs] with z hz
    exact deriv_slowEulerIntegral q m z hq hz
  have hqq : q + 1 + 1 = q + 2 := by ring
  simpa only [neg_neg, hqq, Nat.add_assoc, show (1 : ℕ) + 1 = 2 from rfl] using
    h.congr_of_eventuallyEq heq

theorem slowEulerIntegral_kummer_equation (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    x * deriv (deriv (slowEulerIntegral q m)) x +
      ((m : ℂ) - x) * deriv (slowEulerIntegral q m) x -
      q * slowEulerIntegral q m x = 0 := by
  rw [(hasDerivAt_deriv_slowEulerIntegral q m x hq hx).deriv,
    deriv_slowEulerIntegral q m x hq hx]
  have h := slowEuler_integral_relation q m x hq hx
  change x * slowEulerIntegral (q + 2) (m + 2) x +
    (x - (m : ℂ)) * slowEulerIntegral (q + 1) (m + 1) x -
      q * slowEulerIntegral q m x = 0 at h
  linear_combination h

end DefocusingNLS

end OAI
