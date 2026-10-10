import OAI.Probability.DilutedSpin.CavityErrorLimit
import OAI.Probability.DilutedSpin.IncrementCavityProxy

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open Filter
open scoped Topology NNReal
lemma cavityIncrementError_tendsto (α : ℝ≥0) (q : ℕ) (C : ℝ) :
    Tendsto (cavityIncrementError α q C) atTop (𝓝 0) := by
  have h1 := (cavityBadRate_tendsto α q).const_mul C
  have h2 := scoreScale_div_succ_tendsto.const_mul 6
  have h3 := (((oneNewRate_tendsto α q).sub_const ((α:ℝ)*(q+1))).abs).const_mul C
  have h4 := (((reservoir_deficit_tendsto α q).sub_const ((α:ℝ)*q)).abs).const_mul C
  have hh := (((h1.add h2).add h3).add h4).add scoreScale_succ_difference_tendsto
  unfold cavityIncrementError
  simpa only [mul_div_assoc,sub_self,abs_zero,mul_zero,add_zero] using hh
end DilutedSpinGlass.UniversalDictionary

end

end OAI
