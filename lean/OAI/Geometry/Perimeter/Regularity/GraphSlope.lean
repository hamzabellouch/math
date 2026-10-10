import OAI.Geometry.Perimeter.Regularity.GraphDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem graphTangentLinear_norm_le {v w : Euc n} (hv : ‖v‖=1)
    (hwv : ‖w-v‖≤1/2) : ‖graphTangentLinear v w‖≤2*‖w-v‖ := by
  have hd : (1/2:ℝ) ≤ inner ℝ w v := inner_near_unit_lower hv hwv
  have hd0 : 0 < inner ℝ w v := by linarith
  apply (graphTangentLinear v w).opNorm_le_bound (mul_nonneg (by norm_num) (norm_nonneg _))
  intro y
  rw [Real.norm_eq_abs,graphTangentLinear_apply,abs_mul,abs_neg,
    abs_of_nonneg (inv_nonneg.mpr hd0.le)]
  have hy : inner ℝ v (y:Euc n)=0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal_singleton_iff_inner_left.mp y.property)
  have he : inner ℝ w (y:Euc n)=inner ℝ (w-v) (y:Euc n) := by rw [inner_sub_left,hy,sub_zero]
  rw [he]
  have hi : (inner ℝ w v)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hd0).mpr (by linarith)
  have hb := abs_real_inner_le_norm (w-v) (y:Euc n)
  calc
    (inner ℝ w v)⁻¹*|inner ℝ (w-v) (y:Euc n)| ≤ 2*|inner ℝ (w-v) (y:Euc n)| :=
      mul_le_mul_of_nonneg_right hi (abs_nonneg _)
    _ ≤ 2*(‖w-v‖*‖y‖) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (2*‖w-v‖)*‖y‖ := by ring

end RPISingularHarnack

end

end OAI
