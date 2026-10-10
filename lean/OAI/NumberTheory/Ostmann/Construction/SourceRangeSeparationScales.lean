import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.SourceRangeSeparation
open Filter

theorem broad_range_gaps_eventually (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧ 4000≤favorableBlockWidth L ∧
      Real.exp ((1/1000:ℝ)*L)<Real.exp ((1/250:ℝ)*L) ∧
      Real.exp ((3/500:ℝ)*L)<favorableBlockWidth L/200 ∧
      3*(2:ℝ)^k*favorableBlockWidth L<Real.exp ((1/20:ℝ)*L)-3 := by
  have hsmall := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100-3/500)).eventually_ge_atTop 201
  have hlarge := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/20-1/100)).eventually_ge_atTop (3*(2:ℝ)^k+4)
  have hwidth := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 4000
  filter_upwards [hsmall,hlarge,hwidth,eventually_gt_atTop (0:ℝ)] with L hs hg hw hL
  change 4000≤favorableBlockWidth L at hw
  refine ⟨hL,hw,Real.exp_lt_exp.mpr (by nlinarith),?_,?_⟩
  · have he := mul_le_mul_of_nonneg_right hs (Real.exp_pos ((3/500:ℝ)*L)).le
    rw [← Real.exp_add,show ((1/100:ℝ)-3/500)*L+(3/500)*L=(1/100)*L by ring] at he
    change 201*Real.exp ((3/500:ℝ)*L)≤favorableBlockWidth L at he
    nlinarith [Real.exp_pos ((3/500:ℝ)*L)]
  · have he := mul_le_mul_of_nonneg_right hg (Real.exp_pos ((1/100:ℝ)*L)).le
    rw [← Real.exp_add,show ((1/20:ℝ)-1/100)*L+(1/100)*L=(1/20)*L by ring] at he
    change (3*(2:ℝ)^k+4)*favorableBlockWidth L≤Real.exp ((1/20:ℝ)*L) at he
    nlinarith

end Ostmann.Construction.SourceRangeSeparation

end

end OAI
