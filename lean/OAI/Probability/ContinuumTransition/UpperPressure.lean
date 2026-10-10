import OAI.Probability.ContinuumTransition.KacBounds

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem physical_kac_pressure_upper {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' n, σ n) ≤ (t^2/8)/8)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    {q : ℕ} (hq : 0 < q)
    (hcoeff : β*(t*a)*(1+kacRowError C S ((q : ℝ)/4))/2 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (h : ℝ) :
    physicalPressure (physicalProfile t (prepend a σ) (prepend S R)) t (β,h) ≤
      Real.log (∑' n, quadraticGrandTerm (physicalProfile t σ R) β (t*h)
        (β*(t*a)*(1+kacRowError C S ((q : ℝ)/4))/2) ((q : ℝ)/4) n)/(t*((q : ℝ)/4)^3)+
      (β*(momentConstant t β (t*h)/2)*(2197*t*kernelHeight*(∑' n, σ n))/t)*
        (384*((cellRadius R₀).toNat : ℝ)/(q : ℝ)) := by
  have ht0 := lt_trans zero_lt_one ht
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hσ' := prepend_nonneg ha hσ
  have hR' := prepend_ge_one hS hR
  have hs' := summable_prepend a hs
  have hsm : 2197*t*kernelHeight*(∑' n, prepend a σ n)/2 ≤ t^2/8 := by
    rw [tsum_prepend a hs]
    nlinarith only [hsmall, sq_nonneg t]
  have hL : Tendsto (fun m : ℕ => (m : ℝ)*(q : ℝ)/2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hq0).atTop_div_const (by norm_num)
  have hlim := (physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ' hR' hs')) ht hβ.le
    (physicalProfile_stable ht0.le hσ' hR' hs' hsm)
    (fun r _ => physicalProfile_le_core ht0.le hσ' hR' r) (h := h)).comp hL
  let Z := ∑' n, quadraticGrandTerm (physicalProfile t σ R) β (t*h)
    (β*(t*a)*(1+kacRowError C S ((q : ℝ)/4))/2) ((q : ℝ)/4) n
  let E := β*(momentConstant t β (t*h)/2)*(2197*t*kernelHeight*(∑' n, σ n))
  have hE : 0 ≤ E := by
    dsimp only [E]
    have hM := (momentConstant_pos ht0 hβ (t*h)).le
    have hK := kernelHeight_pos.le
    have hs0 : 0 ≤ ∑' n, σ n := tsum_nonneg hσ
    positivity
  have hrhs := ((grid_card_ratio_tendsto hq).const_mul (Real.log Z/t)).add
    ((boundary_polynomial_ratio_tendsto hq (cellRadius R₀).toNat).const_mul (E/t))
  have hb : physicalPressure (physicalProfile t (prepend a σ) (prepend S R)) t (β,h) ≤
      (Real.log Z/t)*(1/((q : ℝ)/4)^3)+(E/t)*(384*((cellRadius R₀).toNat : ℝ)/(q : ℝ)) := by
    apply le_of_tendsto_of_tendsto hlim hrhs
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hvol : 0 < t*((m : ℝ)*(q : ℝ)/2)^3 := by positivity
    have hh := physical_kac_log_upper hC ht0 hβ ha hS hσ hR hs hsmall hR₀ hbound hq hcoeff m h
    have hcard : ((boundaryIndices m q (cellRadius R₀).toNat).card : ℝ) ≤
        3*((2*(m : ℝ)+1)*(2*((cellRadius R₀).toNat : ℝ)))*(2*(m : ℝ)*(q : ℝ)+1)^2 := by
      exact_mod_cast card_boundaryIndices_le m q (cellRadius R₀).toNat hq
    have hbdy := mul_le_mul_of_nonneg_left hcard hE
    have he : β*(momentConstant t β (t*h)/2)*(boundaryIndices m q (cellRadius R₀).toNat).card*
        (2197*t*kernelHeight*(∑' n, σ n)) = E*(boundaryIndices m q (cellRadius R₀).toNat).card := by
      dsimp only [E]; ring
    rw [he] at hh
    have htotal := hh.trans (add_le_add (le_refl ((gridIndices m 1).card*Real.log Z)) hbdy)
    have hd := (div_le_div_of_nonneg_right htotal hvol.le)
    convert hd using 1 <;> simp only [Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [Z, E, one_div, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm, one_mul] using hb

end ContinuumTemperature
end

end OAI
