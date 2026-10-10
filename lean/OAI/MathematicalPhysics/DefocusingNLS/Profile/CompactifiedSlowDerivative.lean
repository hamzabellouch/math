import OAI.MathematicalPhysics.DefocusingNLS.Profile.CompactifiedSlowContinuity
import Mathlib.Analysis.Calculus.FDeriv.Extend

namespace OAI

/-! # A regular derivative recurrence at inverse radius zero -/

open Filter Topology Set

namespace DefocusingNLS

attribute [local irreducible] normalizedSlowSolution

theorem hasDerivAt_compactifiedSlowSolution_pos (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (compactifiedSlowSolution q m x)
      (q * ((m : ℂ) - 1 - q) / x * compactifiedSlowSolution (q + 1) m x t) t := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hy0 : x / (t : ℂ) ≠ 0 := div_ne_zero hx0 ht0
  have ha : HasDerivAt (fun u : ℝ => x / (u : ℂ)) (-x / (t : ℂ) ^ 2) t := by
    convert! (((hasDerivAt_const (t : ℂ) x).div (hasDerivAt_id (t : ℂ)) ht0).comp_ofReal) using 1
    simp only [id_eq]
    ring
  have hn := hasDerivAt_normalizedSlowSolution q m (x / (t : ℂ)) hq
    (slow_div_real_re_nonneg hx ht) hy0
  have he : compactifiedSlowSolution q m x =ᶠ[𝓝 t]
      (fun u : ℝ => normalizedSlowSolution q m (x / (u : ℂ))) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact compactifiedSlowSolution_pos q m x hu
  convert! (hn.comp t ha).congr_of_eventuallyEq he using 1
  rw [compactifiedSlowSolution_pos (q + 1) m x ht]
  field_simp

/-- The derivative at the endpoint is obtained from the actual normalized
integral and its limit, not imposed as a formal asymptotic coefficient. -/
theorem hasDerivWithinAt_compactifiedSlowSolution_zero (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    HasDerivWithinAt (compactifiedSlowSolution q m x)
      (q * ((m : ℂ) - 1 - q) / x) (Ici 0) 0 := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioi 0)
    (fun t ht => (hasDerivAt_compactifiedSlowSolution_pos q m x hq hx hx0 ht).differentiableAt.differentiableWithinAt)
    (continuousWithinAt_compactifiedSlowSolution_zero q m x hq hx hx0) self_mem_nhdsWithin
  have hc := (continuousWithinAt_compactifiedSlowSolution_zero (q + 1) m x hq' hx hx0).const_mul
    (q * ((m : ℂ) - 1 - q) / x)
  have he : (fun t : ℝ => deriv (compactifiedSlowSolution q m x) t) =ᶠ[𝓝[>] 0]
      (fun t => q * ((m : ℂ) - 1 - q) / x * compactifiedSlowSolution (q + 1) m x t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hasDerivAt_compactifiedSlowSolution_pos q m x hq hx hx0 ht).deriv
  simpa only [compactifiedSlowSolution_zero, mul_one] using hc.congr' he.symm

theorem hasDerivWithinAt_compactifiedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {t : ℝ} (ht : t ∈ Ici 0) :
    HasDerivWithinAt (compactifiedSlowSolution q m x)
      (q * ((m : ℂ) - 1 - q) / x * compactifiedSlowSolution (q + 1) m x t) (Ici 0) t := by
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with he | ht
  · subst t
    simpa only [compactifiedSlowSolution_zero, mul_one] using
      hasDerivWithinAt_compactifiedSlowSolution_zero q m x hq hx hx0
  · exact (hasDerivAt_compactifiedSlowSolution_pos q m x hq hx hx0 ht).hasDerivWithinAt

end DefocusingNLS

end OAI
