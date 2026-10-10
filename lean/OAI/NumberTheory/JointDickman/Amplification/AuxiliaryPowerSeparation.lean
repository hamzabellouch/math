import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryCofactorScales

namespace OAI

/-! # Strict power gaps absorb the fixed endpoint dilations -/
namespace JointDickman
open Filter
open scoped Topology

lemma eventually_scaled_power_lt {c d A B : ℝ} (hcd : c < d)
    (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ X : ℝ in atTop, (A*X)^c < (X/B)^d := by
  have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hcd)).const_mul (A^c*B^d)
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (0:ℝ)] with X hsmall hX
  have he : (A*X)^c/(X/B)^d=(A^c*B^d)*X^(-(d-c)) := by
    rw [Real.mul_rpow hA.le hX.le,Real.div_rpow hX.le hB.le,
      show -(d-c)=c-d by ring,Real.rpow_sub hX]
    field_simp
  rw [← he] at hsmall
  exact (div_lt_one (Real.rpow_pos_of_pos (div_pos hX hB) d)).mp hsmall

end JointDickman

end OAI
