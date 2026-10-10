import OAI.Probability.ContinuumTransition.PhysicalPerturbation

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_coercive {t β L : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (N : ℕ) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3)*((N : ℝ)/L^3)^2 +
      ((N : ℝ)/L^3)*Real.log ((N : ℝ)/L^3)-(β*t^2/2+1)*((N : ℝ)/L^3) ≤
      finiteCanonical (physicalProfile t σ R) β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  have hh := neg_log_partition_lower hφ hβ hL hst hN
    (physicalProfile_energy_coercive ht hL.le hσ hR hs hsmall N)
  have hd := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  convert hd using 1; try rfl
  field_simp
  ring

theorem canonicalDensity_lower_coercive {t β d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (hd : 0 ≤ d) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)*d^2 +
      d*Real.log d-(β*t^2/2+1)*d ≤ canonicalDensity (physicalProfile t σ R) β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0 hσ hR hs hsmall
  have hcore (r : ℝ) (_ : 0 < r) := physicalProfile_le_core ht0 hσ hR r
  have hlim := finiteCanonical_tendsto hφ ht hβ hst hcore hd
  have hi := tendsto_inv_atTop_zero.comp (densityFilter_length d)
  have hc : Tendsto (fun p : ℝ × ℕ =>
      (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/p.1)^3)
      (densityFilter d) (𝓝 ((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)) := by
    have hh := (tendsto_const_nhds (x := t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)).div
      ((tendsto_const_nhds.add (hi.const_mul 2)).pow 3)
      (by norm_num : (4+2*(0 : ℝ))^3 ≠ 0)
    change Tendsto (fun p : ℝ × ℕ =>
      (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2*(p.1)⁻¹)^3)
      (densityFilter d) (𝓝 ((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/((4+2*(0 : ℝ))^3))) at hh
    simpa only [mul_zero, add_zero, div_eq_mul_inv, Function.comp_def, Pi.mul_apply, Pi.inv_apply,
      show (4 : ℝ)^3 = 64 by norm_num] using hh
  have he := (((hc.const_mul β).mul ((densityFilter_density d).pow 2)).add
    (Real.continuous_mul_log.continuousAt.tendsto.comp (densityFilter_density d))).sub
    ((densityFilter_density d).const_mul (β*t^2/2+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  exact finiteCanonical_lower_coercive ht0 hβ hp hσ hR hs hsmall p.2

end ContinuumTemperature
end

end OAI
