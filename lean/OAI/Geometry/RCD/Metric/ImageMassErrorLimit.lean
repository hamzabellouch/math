import OAI.Geometry.RCD.Metric.ImageMassDensityBound

namespace OAI

/-! # Removing both errors in the image-mass density bound -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem unit_volume_le_density_of_image_bounds (n : ℕ) (ω θ A G : ℝ) (hG : 0 ≤ G)
    (hbound : ∀ η : ℝ, 0 < η → η ≤ 1/8192 → ∀ ζ : ℝ, 0 < ζ → ζ*G < 1 →
      ω/(4096:ℝ)^n-ω*A*ζ ≤ (1+32*η)^n*(θ*(1/4096+η/2)^n)) : ω ≤ θ := by
  let e := fun k : ℕ => 1/((k:ℝ)+1)
  have he (k : ℕ) : 0 < e k := by dsimp only [e]; positivity
  have he1 (k : ℕ) : e k ≤ 1 := by
    dsimp only [e]
    apply (div_le_one (by positivity)).mpr
    linarith only [Nat.cast_nonneg (α := ℝ) k]
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let η := fun k => e k/8192
  let ζ := fun k => e k/(2*(G+1))
  have hη0 : Tendsto η atTop (𝓝 0) := by simpa only [zero_div] using he0.div_const 8192
  have hζ0 : Tendsto ζ atTop (𝓝 0) := by simpa only [zero_div] using he0.div_const (2*(G+1))
  have hb (k : ℕ) : ω/(4096:ℝ)^n-ω*A*ζ k ≤
      (1+32*η k)^n*(θ*(1/4096+η k/2)^n) := by
    apply hbound (η k) (by dsimp only [η]; positivity)
      (by dsimp only [η]; exact div_le_div_of_nonneg_right (he1 k) (by norm_num))
      (ζ k) (by dsimp only [ζ]; positivity)
    dsimp only [ζ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_one (by positivity : 0 < 2*(G+1))).mpr
    have hm := mul_le_mul_of_nonneg_right (he1 k) hG
    nlinarith only [hm,hG]
  have hleft : Tendsto (fun k => ω/(4096:ℝ)^n-ω*A*ζ k) atTop (𝓝 (ω/(4096:ℝ)^n)) := by
    simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (hζ0.const_mul (ω*A))
  have hc : Continuous (fun t : ℝ => (1+32*t)^n*(θ*(1/4096+t/2)^n)) := by fun_prop
  have hright : Tendsto (fun k => (1+32*η k)^n*(θ*(1/4096+η k/2)^n))
      atTop (𝓝 (θ/(4096:ℝ)^n)) := by
    simpa only [Function.comp_def,mul_zero,add_zero,zero_div,one_pow,one_mul,
      one_div_pow,mul_one_div] using (hc.tendsto 0).comp hη0
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < (4096:ℝ)^n)).mp
    (le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hb))

end RegularPointCoordinates

end

end OAI
