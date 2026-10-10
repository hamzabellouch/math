import OAI.MeasureTheory.Falconer.Estimates.SamplingScales

namespace OAI

/-! Convert the sampler's exact cardinality bounds to the dyadic lower
and upper powers used by the regular product theorem. -/
namespace Falconer

theorem half_power_rpow_exp (N : ℕ) (s : ℝ) :
    ((1/2:ℝ)^N)^s = Real.exp (-s*(N:ℝ)*Real.log 2) := by
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,
    Real.log_div (by norm_num) (by norm_num),Real.log_one]
  congr 1
  ring

theorem sampled_row_cardinality_bounds (N : ℕ) {s ε : ℝ} (hs : 0 ≤ s)
    (hD : 2 ≤ Real.exp (ε*(N:ℝ)*Real.log 2)) :
    let α := (1/2:ℝ)^N
    let D := Real.exp (ε*(N:ℝ)*Real.log 2)
    ((Nat.ceil (α^(-s)):ℕ):ℝ) ≤ Real.exp ((s+ε)*(N:ℝ)*Real.log 2) ∧
      ∀ m : ℝ, 1 ≤ D*α^s*m → Real.exp ((s-ε)*(N:ℝ)*Real.log 2) ≤ m := by
  dsimp only
  let α := (1/2:ℝ)^N
  let D := Real.exp (ε*(N:ℝ)*Real.log 2)
  let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
  let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hαs : 0 < α^s := Real.rpow_pos_of_pos hα _
  have hU : U*α^s = D := by
    change Real.exp ((s+ε)*(N:ℝ)*Real.log 2)*((1/2:ℝ)^N)^s = _
    rw [half_power_rpow_exp,← Real.exp_add]
    congr 1
    ring
  have hL : (D*α^s)*L = 1 := by
    change (Real.exp (ε*(N:ℝ)*Real.log 2)*((1/2:ℝ)^N)^s)*
      Real.exp ((s-ε)*(N:ℝ)*Real.log 2) = 1
    rw [half_power_rpow_exp,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  constructor
  · have hh := (sampling_ceil_size hα hα1 hs).2.2
    apply (mul_le_mul_iff_left₀ hαs).1
    change ((Nat.ceil (α^(-s)):ℕ):ℝ)*α^s ≤ U*α^s
    rw [hU]
    exact hh.trans hD
  · intro m hm
    have hc : 0 < D*α^s := mul_pos (Real.exp_pos _) hαs
    apply (mul_le_mul_iff_right₀ hc).1
    change (D*α^s)*L ≤ (D*α^s)*m
    rwa [hL]

end Falconer

end OAI
