import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArray
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem adaptive_small_mesh_absorb {Z : ℕ} (hZ : 1 ≤ Z) {K : ℝ}
    (hK : 10 ≤ K) (hKlog : K ≤ Real.log (Z:ℝ)) :
    Real.exp (-K)+(Z:ℝ)^(-(80:ℝ)) ≤ Real.exp (-(9/10:ℝ)*K) := by
  have hz : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by omega)
  have hlog : 0 ≤ Real.log (Z:ℝ) := Real.log_nonneg (by exact_mod_cast hZ)
  have herr : (Z:ℝ)^(-(80:ℝ)) ≤ Real.exp (-K) := by
    rw [Real.rpow_def_of_pos hz]
    apply Real.exp_le_exp.mpr
    linarith
  have htwo : (2:ℝ) ≤ Real.exp (K/10) := by
    have h := Real.add_one_le_exp (K/10)
    linarith
  have he : Real.exp (K/10)*Real.exp (-K)=Real.exp (-(9/10:ℝ)*K) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ 2*Real.exp (-K) := by linarith
    _ ≤ Real.exp (K/10)*Real.exp (-K) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := he

theorem eventually_auxiliary_small_grid_absorption :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      10 ≤ (auxiliaryK Z z:ℝ) ∧ (auxiliaryK Z z:ℝ) ≤ Real.log Z := by
  filter_upwards [eventually_auxiliaryK_bounds,eventually_auxiliaryK_le_log 1 (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 10]
    with T hbound hlog hT
  intro Z z hZl hZu hz hzl hzu
  refine ⟨hT.trans (hbound Z z hZl hZu hz hzl hzu).1,?_⟩
  simpa only [one_mul] using hlog Z z hZl hZu hz hzl hzu

end Ostmann.QuadraticCenter

end

end OAI
