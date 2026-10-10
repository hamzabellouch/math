import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeClassBound

namespace OAI

/-! Geometric summation for the two discarded amplitude tails. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_zpow_sum_bound (S : Finset ℤ) (b R : ℝ) (hb : 1<b) (hR : 0≤R)
    (hbound : ∀ i∈S, b^i≤R) :
    (∑ i∈S, b^i)≤(2/(1-b⁻¹))*R := by
  classical
  have hb0 : 0<b := zero_lt_one.trans hb
  have hr : 0≤b⁻¹ := inv_nonneg.mpr hb0.le
  have hr1 : b⁻¹<1 := inv_lt_one_of_one_lt₀ hb
  have hC : 0≤2/(1-b⁻¹) := by positivity
  by_cases hS : S.Nonempty
  · let j := S.max' hS
    have hj : j∈S := Finset.max'_mem S hS
    have heq (i : ℤ) (hi : i∈S) : b^i=b^j*(b⁻¹)^(i-j).natAbs := by
      have hij : i≤j := Finset.le_max' S i hi
      have hn : ((i-j).natAbs:ℤ)=j-i := by omega
      rw [←zpow_natCast,inv_zpow,←zpow_neg,hn,←zpow_add₀ hb0.ne']
      congr 1
      omega
    calc
      _ = b^j*(∑ i∈S, (b⁻¹)^(i-j).natAbs) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl heq
      _ ≤ b^j*(2/(1-b⁻¹)) := mul_le_mul_of_nonneg_left
        (int_geometric_shift_sum_le hr hr1 S j) (zpow_pos hb0 _).le
      _ ≤ (2/(1-b⁻¹))*R := by nlinarith [hbound j hj]
  · have hEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [Finset.sum_empty]
    exact mul_nonneg hC hR

theorem sqrt_two_zpow (i : ℤ) : (Real.sqrt 2)^i=Real.sqrt ((2:ℝ)^i) := by
  have hs : ((Real.sqrt 2)^i)^2=(2:ℝ)^i := by
    rw [←zpow_natCast,←zpow_mul,mul_comm,zpow_mul,zpow_natCast,
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [←hs,Real.sqrt_sq_eq_abs,abs_of_pos (zpow_pos (Real.sqrt_pos.2 (by norm_num)) _)]

end LipschitzHilbert

end

end OAI
