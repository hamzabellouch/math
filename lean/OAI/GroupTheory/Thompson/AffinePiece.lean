import OAI.GroupTheory.Thompson.IntervalCharts

namespace OAI

/-!
# Affine maps between basic dyadic intervals

Each pair of basic intervals determines an increasing affine map of the real
line. It carries endpoints and charts to their counterparts, and its slope is
an integral power of two.
-/

noncomputable section

namespace ThompsonNonamenability

namespace OrderedPLInterpolation

def affine (I J : BasicInterval) (x : ℝ) : ℝ :=
  J.left + (J.length / I.length) * (x - I.left)

@[simp] theorem affine_left (I J : BasicInterval) :
    affine I J I.left = J.left := by
  simp [affine]

@[simp] theorem affine_right (I J : BasicInterval) :
    affine I J I.right = J.right := by
  unfold affine
  rw [← I.length_eq_right_sub_left]
  rw [div_mul_cancel₀ _ (ne_of_gt I.length_pos)]
  rw [J.length_eq_right_sub_left]
  ring

theorem affine_strictMono (I J : BasicInterval) : StrictMono (affine I J) := by
  intro x y hxy
  exact add_lt_add_right
    (mul_lt_mul_of_pos_left (sub_lt_sub_right hxy I.left)
      (div_pos J.length_pos I.length_pos)) J.left

@[simp] theorem affine_inverse (I J : BasicInterval) (x : ℝ) :
    affine J I (affine I J x) = x := by
  unfold affine
  field_simp [ne_of_gt I.length_pos, ne_of_gt J.length_pos]
  ring

@[simp] theorem affine_chart (I J : BasicInterval) (x : ℝ) :
    affine I J (I.chart x) = J.chart x := by
  rw [I.chart_eq_left_add_length_mul, J.chart_eq_left_add_length_mul]
  unfold affine
  field_simp [ne_of_gt I.length_pos]
  ring

theorem affine_slope_zpow (I J : BasicInterval) :
    J.length / I.length = (2 : ℝ) ^ ((I.depth : ℤ) - (J.depth : ℤ)) := by
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast, BasicInterval.length, inv_div_inv]

end OrderedPLInterpolation

end ThompsonNonamenability

end

end OAI
