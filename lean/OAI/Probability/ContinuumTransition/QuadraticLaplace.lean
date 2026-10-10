import OAI.Probability.ContinuumTransition.QuadraticGrand

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def quadraticPressure (φ : ℝ → ℝ) (β μ a : ℝ) : ℝ :=
  sSup ((fun d : ℝ => μ*d+a*d^2-canonicalDensity φ β d) '' Ici 0)

theorem quadraticPressure_bddAbove {t β μ a : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)) :
    BddAbove ((fun d : ℝ => μ*d+a*d^2-canonicalDensity (physicalProfile t σ R) β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*t^2/2), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_coercive ht hβ hσ hR hs hsmall hd
  have he := entropy_dual_bound (μ+β*t^2/2) hd
  have hq := mul_le_mul_of_nonneg_right ha (sq_nonneg d)
  linarith

theorem coerciveCoefficient_tendsto (c : ℝ) :
    Tendsto (fun L : ℝ => c/(4+2/L)^3) atTop (𝓝 (c/64)) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hh := (tendsto_const_nhds (x := c)).div
    ((tendsto_const_nhds.add (hi.const_mul 2)).pow 3)
    (by norm_num : (4+2*(0 : ℝ))^3 ≠ 0)
  change Tendsto (fun L : ℝ => c/(4+2*L⁻¹)^3) atTop (𝓝 (c/(4+2*(0 : ℝ))^3)) at hh
  simpa only [mul_zero, add_zero, div_eq_mul_inv, show (4 : ℝ)^3=64 by norm_num] using hh

theorem quadraticGrand_pressure_tendsto {t β μ a : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a < β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64))
    {aL : ℝ → ℝ} (haL : Tendsto aL atTop (𝓝 a)) :
    Tendsto (fun L => Real.log (∑' n, quadraticGrandTerm (physicalProfile t σ R) β μ (aL L) L n)/L^3)
      atTop (𝓝 (quadraticPressure (physicalProfile t σ R) β μ a)) := by
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0 hσ hR hs hsmall
  have hcore (r : ℝ) (_ : 0 < r) := physicalProfile_le_core ht0 hσ hR r
  have hcoeff := coerciveCoefficient_tendsto (β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2))
  have ha' : a < β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64 := by
    simpa only [mul_div_assoc] using ha
  have hev := haL.eventually_lt hcoeff ha'
  have hsum : ∀ᶠ L in atTop,
      Summable (quadraticGrandTerm (physicalProfile t σ R) β μ (aL L) L) := by
    filter_upwards [hev, eventually_gt_atTop 0] with L hL hp
    exact summable_quadraticGrandTerm ht0 hβ hp hσ hR hs hsmall hL.le
  have hw (L : ℝ) (hL : 0 < L) (n : ℕ) := quadraticGrandTerm_pos hφ hβ hL hst μ (aL L) n
  have hb : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  have hz : μ*0+a*0^2-canonicalDensity (physicalProfile t σ R) β 0 = 0 := by
    rw [canonicalDensity_zero hφ ht hβ hst hcore]; ring
  have hlim : ∀ d, 0 ≤ d →
      Tendsto (fun p : ℝ × ℕ => Real.log (quadraticGrandTerm (physicalProfile t σ R) β μ (aL p.1) p.1 p.2)/p.1^3)
        (densityFilter d) (𝓝 (μ*d+a*d^2-canonicalDensity (physicalProfile t σ R) β d)) := by
    intro d hd
    have hh := (((densityFilter_density d).const_mul μ).add
      ((haL.comp (densityFilter_length d)).mul ((densityFilter_density d).pow 2))).sub
      (finiteCanonical_tendsto hφ ht hβ hst hcore hd)
    apply hh.congr'
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
    exact (log_quadraticGrandTerm hφ hβ hp hst μ (aL p.1) p.2).symm
  have htail : ∀ᶠ L in atTop, ∀ n : ℕ, Real.exp (μ+β*t^2/2+2) ≤ (n : ℝ)/L^3 →
      quadraticGrandTerm (physicalProfile t σ R) β μ (aL L) L n ≤ (Real.exp (-1))^n := by
    filter_upwards [hev, eventually_gt_atTop 0] with L hL hp
    exact fun _ hn => quadraticGrandTerm_high_density ht0 hβ hp hσ hR hs hsmall hL.le hn
  exact laplace_principle_eventual hw hsum hb (fun n => (pow_pos (Real.exp_pos _) n).le)
    (Real.exp_pos (μ+β*t^2/2+2)) hz (quadraticPressure_bddAbove ht hβ hσ hR hs hsmall ha.le) hlim htail

end ContinuumTemperature
end

end OAI
