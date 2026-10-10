import OAI.Probability.ContinuumTransition.LowerBounds

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem physical_kac_pressure_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    {q : ℕ} (hq : 0 < q) (hu : 2 < (q : ℝ)/4) (n : ℕ) (h : ℝ) :
    (t*h*((n : ℝ)/((q : ℝ)/4)^3)+
      Real.log (partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)/((q : ℝ)/4)^3+
      β*(t*a)/2*(((n : ℝ)/((q : ℝ)/4)^3)^2*(1-kacRowError C S ((q : ℝ)/4))-
        ((n : ℝ)/((q : ℝ)/4)^3)*scaledKernel S 0))/t ≤
      physicalPressure (physicalProfile t (prepend a σ) (prepend S R)) t (β,h) := by
  have ht0 := lt_trans zero_lt_one ht
  have hu0 : 0 < (q : ℝ)/4 := by positivity
  obtain ⟨N, hN'⟩ := exists_nat_ge ((S+(q : ℝ)/4)/((q : ℝ)/4))
  have hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4) := (div_le_iff₀ hu0).1 hN'
  have hσ' := prepend_nonneg ha hσ
  have hR' := prepend_ge_one hS hR
  have hs' := summable_prepend a hs
  have hsm : 2197*t*kernelHeight*(∑' j, prepend a σ j)/2 ≤ t^2/8 := by
    rw [tsum_prepend a hs]
    nlinarith only [hsmall, sq_nonneg t]
  have hL : Tendsto (fun m : ℕ => 2*((m+N : ℕ)+1)*((q : ℝ)/4)) atTop atTop := by
    have hh := (((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N+1))).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2))).atTop_mul_const hu0
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_assoc] using hh
  have hright := (physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ' hR' hs')) ht hβ.le
    (physicalProfile_stable ht0.le hσ' hR' hs' hsm)
    (fun r _ => physicalProfile_le_core ht0.le hσ' hR' r) (h := h)).comp hL
  let u := (q : ℝ)/4
  let A := (t*h*n+Real.log (partition (physicalProfile t σ R) β (u-2) n))
  let B := (n : ℝ)^2*((1-kacRowError C S u)/u^3)
  let D := (n : ℝ)*scaledKernel S 0
  have hrat₀ := grid_card_outer_ratio_tendsto hu0 0 N
  have hratN := grid_card_outer_ratio_tendsto hu0 N N
  have hleft := (((hrat₀.const_mul B).sub (hratN.const_mul D)).const_mul (β*(t*a)/2)).add
    (hratN.const_mul A)
  have hb := le_of_tendsto_of_tendsto (hleft.div_const t) hright
    (Filter.Eventually.of_forall (fun m : ℕ => ?_))
  · refine le_trans ?_ hb
    apply le_of_eq
    dsimp only [A,B,D,u]
    ring
  have hh := physical_kac_log_lower hC ht hβ ha hS hσ hR hs hsmall hq hu (m := m) hN n h
  have hv : 0 < t*(2*((m+N : ℕ)+1)*u)^3 := by dsimp only [u]; positivity
  have hd := div_le_div_of_nonneg_right hh hv.le
  convert hd using 1 <;> simp only [Function.comp_apply, Nat.add_zero, kacLowerGain, A, B, D, u,
    div_eq_mul_inv, mul_inv_rev]
  ring

end ContinuumTemperature
end

end OAI
