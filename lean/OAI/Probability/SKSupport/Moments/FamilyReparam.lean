import Mathlib
import OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma scaled_composition_jet {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) (n : ℕ) (x : ℝ) :
    _root_.iteratedDeriv n (fun y => f (a*y)) x = a^n*_root_.iteratedDeriv n f (a*x) := by
  exact congrFun (iteratedDeriv_comp_const_mul
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) a) x

lemma BoundedSmoothFamily.reparam {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F)
    {A C : ℝ → ℝ} (hA : Measurable A) (hC : Measurable C) (hb : ∀ t, |C t| ≤ 1) :
    BoundedSmoothFamily (fun t x => F (A t) (C t*x)) := by
  have hbound (n : ℕ) : ∃ K : ℝ≥0, ∀ t x,
      |_root_.iteratedDeriv n (fun y => F (A t) (C t*y)) x| ≤ K := by
    obtain ⟨K,hK⟩ := hF.bounds n
    refine ⟨K,fun t x => ?_⟩
    rw [scaled_composition_jet (hF.regular (A t)).smooth,abs_mul,abs_pow]
    calc
      |C t|^n*|_root_.iteratedDeriv n (F (A t)) (C t*x)| ≤ 1*(K:ℝ) :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) (hb t)) (hK _ _) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  refine ⟨hF.measurable.comp ((hA.comp measurable_fst).prodMk
    ((hC.comp measurable_fst).mul measurable_snd)),?_,hbound⟩
  intro t
  refine ⟨(hF.regular (A t)).smooth.comp (contDiff_const.mul contDiff_id),?_⟩
  intro n
  obtain ⟨K,hK⟩ := hbound n
  exact ⟨K,hK t⟩

lemma BoundedSmoothFamily.timeMul {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F)
    {C : ℝ → ℝ} {K : ℝ≥0} (hC : Measurable C) (hb : ∀ t, |C t| ≤ K) :
    BoundedSmoothFamily (fun t x => C t*F t x) :=
  (BoundedSmoothFamily.timeConst hC hb).mul hF

end ZeroTemperatureSK.Heat

end
end

end OAI
