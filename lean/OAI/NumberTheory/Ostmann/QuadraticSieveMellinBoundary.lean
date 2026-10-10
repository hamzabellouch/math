import OAI.NumberTheory.Ostmann.QuadraticSieveMellinConvergence

namespace OAI

namespace Ostmann
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap

theorem schwartz_cpow_mul_tendsto_zero (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * ρ x) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hp : Tendsto (fun x : ℝ => x ^ s.re) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt hs)] using
      ((Real.continuous_rpow_const hs.le).tendsto 0).mono_left nhdsWithin_le_nhds
  have hρ : Tendsto (fun x : ℝ => ‖ρ x‖) (𝓝[>] 0) (𝓝 ‖ρ 0‖) :=
    (ρ.continuous.norm.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := hp.mul hρ
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem schwartz_cpow_mul_tendsto_atTop (ρ : 𝓢(ℝ, ℂ)) (s : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * ρ x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb := (isBigO_refl (fun x : ℝ => x ^ s.re) atTop).mul
    (schwartz_isBigO_rpow_atTop ρ (-s.re - 1)).norm_left
  have hb' : (fun x : ℝ => x ^ s.re * ‖ρ x‖) =O[atTop]
      (fun x : ℝ => x ^ (-(1 : ℝ))) := by
    apply hb.congr' Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have h := hb'.trans_tendsto (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

end Ostmann

end OAI
