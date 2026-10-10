import OAI.Probability.ContinuumTransition.LowerPressure

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

noncomputable def kacTrialValue (φ : ℝ → ℝ) (C : NNReal) (t β a h d u : ℝ) : ℝ :=
  let n := ⌊d*(u-2)^3⌋₊
  (t*h*((n : ℝ)/u^3)+Real.log (partition φ β (u-2) n)/u^3+
    β*(t*a)/2*(((n : ℝ)/u^3)^2*(1-kacRowError C (u^2) u)-
      ((n : ℝ)/u^3)*scaledKernel (u^2) 0))/t

theorem kacTrialValue_tendsto {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (C : NNReal) (a h : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (kacTrialValue φ C t β a h d) atTop
      (𝓝 ((t*h*d-canonicalDensity φ β d+β*(t*a)/2*d^2)/t)) := by
  have hi : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hℓ : Tendsto (fun u : ℝ => u-2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_id
  have hr : Tendsto (fun u : ℝ => (u-2)^3/u^3) atTop (𝓝 1) := by
    have hh := ((hi.const_mul 2).const_sub 1).pow 3
    have he : Tendsto (fun u : ℝ => (1-2*u⁻¹)^3) atTop (𝓝 1) := by simpa using hh
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  have hden := ((tendsto_densityFilter_iff.mp (floor_density_tendsto hd)).2).comp hℓ
  have hn : Tendsto (fun u : ℝ => (⌊d*(u-2)^3⌋₊ : ℝ)/u^3) atTop (𝓝 d) := by
    have hh : Tendsto (fun u : ℝ => ((⌊d*(u-2)^3⌋₊ : ℝ)/(u-2)^3)*((u-2)^3/u^3))
        atTop (𝓝 d) := by simpa only [mul_one, Function.comp_apply] using hden.mul hr
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with u hu
    have hne : u-2 ≠ 0 := (sub_pos.mpr hu).ne'
    field_simp
  have hc := (finiteCanonical_tendsto hφ ht hβ hst hcore hd).comp ((floor_density_tendsto hd).comp hℓ)
  have hz : Tendsto (fun u : ℝ => Real.log (partition φ β (u-2) ⌊d*(u-2)^3⌋₊)/u^3)
      atTop (𝓝 (-canonicalDensity φ β d)) := by
    have hh : Tendsto (fun u : ℝ => -finiteCanonical φ β (u-2) ⌊d*(u-2)^3⌋₊*((u-2)^3/u^3))
        atTop (𝓝 (-canonicalDensity φ β d)) := by
      simpa only [mul_one, Function.comp_apply] using hc.neg.mul hr
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with u hu
    have hne : u-2 ≠ 0 := (sub_pos.mpr hu).ne'
    unfold finiteCanonical
    field_simp
  have hw : Tendsto (fun u : ℝ => scaledKernel (u^2) 0) atTop (𝓝 0) := by
    simpa [scaledKernel, scaledKernelProfile] using ((hi.pow 2).pow 3).mul_const (kernelProfile 0)
  have he := (((hn.const_mul (t*h)).add hz).add
    ((((hn.pow 2).mul ((kacRowError_sq_tendsto C).const_sub 1)).sub
      (hn.mul hw)).const_mul (β*(t*a)/2))).div_const t
  convert he using 1 <;> first | rfl | (congr 1; ring)

theorem physical_kac_lower_density_eventually {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    (h : ℝ) {d : ℝ} (hd : 0 ≤ d) {c : ℝ}
    (hc : c < (t*h*d-canonicalDensity (physicalProfile t σ R) β d+β*(t*a)/2*d^2)/t) :
    ∀ᶠ q : ℕ in atTop, c <
      physicalPressure (physicalProfile t (prepend a σ) (prepend (((q : ℝ)/4)^2) R)) t (β,h) := by
  have ht0 := lt_trans zero_lt_one ht
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' j, σ j)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hh := (kacTrialValue_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht hβ.le
    (physicalProfile_stable ht0.le hσ hR hs hsm)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r) C a h hd).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  filter_upwards [hh.eventually_const_lt hc, eventually_ge_atTop (12 : ℕ)] with q hq hq12
  have hq0 : 0 < q := by omega
  have hu : 2 < (q : ℝ)/4 := by
    have hq' : (12 : ℝ) ≤ q := by exact_mod_cast hq12
    linarith
  have hS : 1 ≤ ((q : ℝ)/4)^2 := by nlinarith
  exact hq.trans_le (physical_kac_pressure_lower hC ht hβ ha hS hσ hR hs hsmall hq0 hu _ h)

end ContinuumTemperature
end

end OAI
