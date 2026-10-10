import OAI.Analysis.FreeEntropy.TerminalGaussian

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set
namespace FiniteEntropySeparation

def reciprocalDifference (a s : ℝ) : ℝ := 1 / (1+s) - 1 / (a+s)
def logarithmicPrimitive (a s : ℝ) : ℝ := Real.log (1+s) - Real.log (a+s)

 theorem logarithmicPrimitive_deriv {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (logarithmicPrimitive a) (reciprocalDifference a s) s := by
  unfold logarithmicPrimitive reciprocalDifference
  have h1 : 1+s ≠ 0 := by linarith
  have h2 : a+s ≠ 0 := by linarith
  convert (((hasDerivAt_id s).const_add 1).log h1).sub (((hasDerivAt_id s).const_add a).log h2) using 1
  all_goals rfl

 theorem logarithmicPrimitive_atTop (a : ℝ) :
    Tendsto (logarithmicPrimitive a) atTop (𝓝 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log 1).sub (Real.tendsto_log_comp_add_sub_log a)
  unfold logarithmicPrimitive
  convert h using 1 <;> simp [add_comm, sub_sub_sub_cancel_right]

 theorem reciprocalDifference_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (reciprocalDifference a) (Ioi 0) := by
  by_cases ha1 : 1 ≤ a
  · apply integrableOn_Ioi_deriv_of_nonneg' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (fun s hs => ?_) (logarithmicPrimitive_atTop a)
    have hs : 0 < s := hs
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by linarith : 0 < 1+s)
    linarith
  · apply integrableOn_Ioi_deriv_of_nonpos' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (fun s hs => ?_) (logarithmicPrimitive_atTop a)
    have hs : 0 < s := hs
    apply sub_nonpos.mpr
    apply one_div_le_one_div_of_le (by linarith : 0 < a+s)
    linarith

 theorem reciprocalDifference_integral {a : ℝ} (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), reciprocalDifference a s = Real.log a := by
  simpa [logarithmicPrimitive] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun s hs => logarithmicPrimitive_deriv ha hs)
      (reciprocalDifference_integrable ha) (logarithmicPrimitive_atTop a)

end FiniteEntropySeparation

end

end OAI
