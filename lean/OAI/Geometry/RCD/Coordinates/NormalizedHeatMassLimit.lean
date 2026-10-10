import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # The heat cutoff mass estimate vanishes after physical normalization -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem normalized_heat_mass_limit
    (r m E v M : ℕ → ℝ) {C K : ℝ}
    (hr : ∀ k, 0 < r k) (hm : ∀ k, 0 < m k)
    (hM : ∀ k, 0 ≤ M k) (hv : ∀ k, v k ≤ m k)
    (hK : K ≤ 0) (hr0 : Tendsto r atTop (𝓝 0))
    (hE0 : Tendsto (fun k => E k/m k) atTop (𝓝 0))
    (hb : ∀ k, M k ≤ (C/(2*r k)^2)/2*E k+
      (-K)*(E k+v k)+m k/((r k)^2*((k:ℝ)+1))) :
    Tendsto (fun k => (r k)^2*M k/m k) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k => C/8*(E k/m k)+
      (-K)*(r k)^2*(E k/m k+1)+1/((k:ℝ)+1)) atTop (𝓝 0) := by
    have hh := ((hE0.const_mul (C/8)).add
      (((hr0.pow 2).const_mul (-K)).mul (hE0.add_const 1))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [zero_pow (by decide : (2:ℕ)≠0),zero_add,mul_zero,zero_mul] using hh
  apply squeeze_zero (fun k => div_nonneg (mul_nonneg (sq_nonneg _) (hM k)) (hm k).le) _ hlim
  intro k
  have hb' : M k ≤ (C/(2*r k)^2)/2*E k+
      (-K)*(E k+m k)+m k/((r k)^2*((k:ℝ)+1)) := by
    have hc := mul_le_mul_of_nonneg_left (hv k) (neg_nonneg.mpr hK)
    linarith only [hb k,hc]
  have hh := mul_le_mul_of_nonneg_left hb' (div_nonneg (sq_nonneg (r k)) (hm k).le)
  convert hh using 1 <;> field_simp [(hr k).ne',(hm k).ne']; ring

end RegularPointCoordinates

end

end OAI
