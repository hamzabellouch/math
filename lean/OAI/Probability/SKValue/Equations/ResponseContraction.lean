import Mathlib
import OAI.Probability.SKValue.Equations.TestPatch

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma responseJet_zero_sub {ψ f g:ℝ → ℝ} (hψ:SmoothTerminal ψ)
    (hf:BoundedSmooth f) (hg:BoundedSmooth g) {c:ℝ} (hc:0 ≤ c) (t x:ℝ) :
    responseJet c ψ f 0 t x-responseJet c ψ g 0 t x=
      responseJet c ψ (fun y ↦ f y-g y) 0 t x := by
  simp only [responseJet,iteratedDeriv_zero,←sub_div]
  congr 1
  unfold heat
  rw [←integral_sub]
  · congr 1;funext y;ring
  · exact (weighted_growth hψ hf hc 0).shift_integrable
      ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth).continuous.measurable x (Real.sqrt t)
  · exact (weighted_growth hψ hg hc 0).shift_integrable
      ((contDiff_const.mul hψ.smooth).exp.mul hg.smooth).continuous.measurable x (Real.sqrt t)
lemma responseJet_zero_contraction {ψ f g:ℝ → ℝ} (hψ:SmoothTerminal ψ)
    (hf:BoundedSmooth f) (hg:BoundedSmooth g) {c C:ℝ} (hc:0 ≤ c)
    (hb:∀ x,|f x-g x| ≤ C) (t x:ℝ) :
    |responseJet c ψ f 0 t x-responseJet c ψ g 0 t x| ≤ C := by
  have hsub:BoundedSmooth (fun y ↦ f y-g y) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))
  rw [responseJet_zero_sub hψ hf hg hc]
  have hp:0<heat t (fun y ↦ Real.exp (c*ψ y)) x := lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)
  rw [responseJet,iteratedDeriv_zero,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  apply heat_relative_bound ((contDiff_const.mul hψ.smooth).exp).continuous.measurable
    (((contDiff_const.mul hψ.smooth).exp).mul hsub.smooth).continuous.measurable
    (ExpGrowth.exp_lipschitz hψ.lipschitz hc) (weighted_growth hψ hsub hc 0)
  intro y
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos (c*ψ y)).le
lemma SmoothTerminal.profile_response_contraction {ψ f g:ℝ → ℝ} (hψ:SmoothTerminal ψ)
    (hf:BoundedSmooth f) (hg:BoundedSmooth g) {C:ℝ}
    (hb:∀ x,|f x-g x| ≤ C) (l:HeatProfile) (t x:ℝ) :
    |profileResponse ψ f l t x-profileResponse ψ g l t x| ≤ C := by
  induction l generalizing t x with
  | nil => exact hb x
  | cons p l ih =>
    simp only [profileResponse]
    by_cases ht:t ≤ (p.1:ℝ)
    · rw [patchTime_left _ _ ht,patchTime_left _ _ ht]
      exact responseJet_zero_contraction
        ((hψ.profile_evolution l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩)
        ((hψ.linear_profile hf l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩)
        ((hψ.linear_profile hg l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩)
        p.2.coe_nonneg (fun y ↦ ih 0 y) _ x
    · rw [patchTime_right _ _ (lt_of_not_ge ht),patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ x
end SKValue

end

end OAI
