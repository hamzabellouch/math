import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleSeries

namespace OAI

/-! Radius-normalized coefficient extraction, with a linear error in the radius. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
variable {ι : Type*} [Countable ι]

theorem cubicThetaCircleSeries_normalized_remainder {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (k : ℕ)
    (hk : Summable (fun n => a n*w n^k))
    (hk1 : Summable (fun n => ‖a n‖*‖w n‖^(k+1))) {r : ℝ} (hr : 0<r) :
    ‖fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)/(r:ℂ)^k-
      ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)‖≤
        (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*
          (∑' n, ‖a n‖*‖w n‖^(k+1)))*r := by
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)/(r:ℂ)^k-
      ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)=
    (fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)-
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*(∑' n, a n*w n^k))/(r:ℂ)^k := by
    rw [mul_pow]
    field_simp [hrC]
    simp only [mul_pow]
    ring
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  apply (div_le_iff₀ (pow_pos hr k)).mpr
  convert cubicThetaCircleSeries_remainder ha k hk hk1 hr.le using 1
  rw [pow_succ]
  ring

theorem cubicThetaCircleSeries_normalized_limit {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (k : ℕ)
    (hk : Summable (fun n => a n*w n^k))
    (hk1 : Summable (fun n => ‖a n‖*‖w n‖^(k+1))) :
    Tendsto (fun r : ℝ => fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)/(r:ℂ)^k)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(∑' n, a n*w n^k))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : ∀ᶠ r : ℝ in 𝓝[Set.Ioi (0:ℝ)] 0,
      ‖fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)/(r:ℂ)^k-
        ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)‖≤
          (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*
            (∑' n, ‖a n‖*‖w n‖^(k+1)))*r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact cubicThetaCircleSeries_normalized_remainder ha k hk hk1 hr
  have ht : Tendsto (fun r : ℝ => (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*
      (∑' n, ‖a n‖*‖w n‖^(k+1)))*r) (𝓝[Set.Ioi (0:ℝ)] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
    Tendsto (fun r : ℝ => (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*
      (∑' n, ‖a n‖*‖w n‖^(k+1)))*r) (𝓝[Set.Ioi 0] 0) (𝓝 (_*0)))
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hb ht

end CubicFirstMoment

end

end OAI
