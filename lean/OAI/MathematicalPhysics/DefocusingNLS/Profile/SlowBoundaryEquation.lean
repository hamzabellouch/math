import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowSpatialBoundary
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace OAI

/-! # The slow differential identities on the imaginary boundary -/

open Filter Topology

namespace DefocusingNLS

theorem eq_zero_on_imaginary_boundary {f : ℂ → ℂ} {x : ℂ} (hx : x.re = 0)
    (hf : ContinuousAt f x) (hzero : ∀ y : ℂ, 0 < y.re → f y = 0) : f x = 0 := by
  have ht : Tendsto (fun t : ℝ => x + (t : ℂ)) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + (t : ℂ)) :=
      continuous_const.add Complex.continuous_ofReal
    simpa only [Complex.ofReal_zero, add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have heq : (fun t : ℝ => f (x + (t : ℂ))) =ᶠ[𝓝[>] 0] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply hzero
    change 0 < x.re + t
    rw [hx, zero_add]
    exact ht
  exact tendsto_nhds_unique (hf.tendsto.comp ht) (tendsto_const_nhds.congr' heq.symm)

theorem regularizedSlowSolution_kummer_equation_closed (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    x * deriv (deriv (regularizedSlowSolution q m)) x +
      ((m : ℂ) - x) * deriv (regularizedSlowSolution q m) x -
        q * regularizedSlowSolution q m x = 0 := by
  rcases hx.eq_or_lt with hx | hx
  · have hxim : x.im ≠ 0 := by
      intro hi
      apply hx0
      apply Complex.ext
      · exact hx.symm
      · exact hi
    have hslit : x ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hxim)
    have ha := analyticOnNhd_regularizedSlowSolution_slit q m hq
    have hc₀ := (ha x hslit).continuousAt
    have hc₁ := (ha.deriv x hslit).continuousAt
    have hc₂ := (ha.deriv.deriv x hslit).continuousAt
    apply eq_zero_on_imaginary_boundary hx.symm
    · exact ((continuousAt_id.mul hc₂).add
        ((continuousAt_const.sub continuousAt_id).mul hc₁)).sub (continuousAt_const.mul hc₀)
    · intro y hy
      exact regularizedSlowSolution_kummer_equation q m y hq hy
  · exact regularizedSlowSolution_kummer_equation q m x hq hx

theorem hasDerivAt_regularizedSlowSolution_shift_closed (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    HasDerivAt (regularizedSlowSolution q m)
      (-q * regularizedSlowSolution (q + 1) (m + 1) x) x := by
  rcases hx.eq_or_lt with hx | hx
  · have hxim : x.im ≠ 0 := by
      intro hi
      apply hx0
      apply Complex.ext
      · exact hx.symm
      · exact hi
    have hslit : x ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hxim)
    have ha := analyticOnNhd_regularizedSlowSolution_slit q m hq
    have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
    have hb := analyticOnNhd_regularizedSlowSolution_slit (q + 1) (m + 1) hq'
    have he : deriv (regularizedSlowSolution q m) x +
        q * regularizedSlowSolution (q + 1) (m + 1) x = 0 := by
      apply eq_zero_on_imaginary_boundary hx.symm
      · exact (ha.deriv x hslit).continuousAt.add
          (continuousAt_const.mul (hb x hslit).continuousAt)
      · intro y hy
        rw [(hasDerivAt_regularizedSlowSolution_shift q m y hq hy).deriv]
        ring
    have hd := (ha x hslit).differentiableAt.hasDerivAt
    convert hd using 1
    linear_combination -he
  · exact hasDerivAt_regularizedSlowSolution_shift q m x hq hx

end DefocusingNLS

end OAI
