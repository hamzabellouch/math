import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterKBounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbabilityBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_auxiliary_witness_expectation_margin :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      1+Real.exp ((7/1000:ℝ)*auxiliaryK Z z)+1+1 ≤
        Real.exp ((3/200:ℝ)*auxiliaryK Z z) := by
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp eventually_witness_expectation_margin
  filter_upwards [eventually_auxiliaryK_bounds,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop K₀]
    with T hK hT
  intro Z z hZl hZu hz hzl hzu
  exact hK₀ _ (hT.trans (hK Z z hZl hZu hz hzl hzu).1)

end Ostmann.QuadraticCenter

end

end OAI
