import OAI.Algebra.AuslanderReiten.Bar.TCasimir

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

@[simp] private theorem coordinateFunctional_apply (i : Letter) (a : BaseAlgebra k q) :
    coordinateFunctional q i a = a.coeff i := rfl

private theorem lower_upper_same (i : Letter) :
    lower q i * upper q i = upper q (if TIndex.lowerSource i then .f else .e) := by
  apply TrivialExtension.ext
  · simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr]
  · apply LinearMap.ext
    intro a
    cases i <;> simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr,
      TIndex.lowerSource, BaseAlgebra.product]

private theorem upper_lower_same (i : Letter) :
    upper q i * lower q i = upper q (if TIndex.lowerTarget i then .f else .e) := by
  apply TrivialExtension.ext
  · simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr]
  · apply LinearMap.ext
    intro a
    cases i <;> simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr,
      TIndex.lowerTarget, BaseAlgebra.product]

variable [CharP k 2]

private theorem six_four_zero (x y : R) :
    x + x + x + x + x + x + y + y + y + y = 0 := by
  have hx := SparseParity.module_add_self_eq_zero (k := k) x
  have hy := SparseParity.module_add_self_eq_zero (k := k) y
  calc
    _ = (x + x) + (x + x) + (x + x) + (y + y) + (y + y) := by abel
    _ = 0 := by rw [hx, hy]; simp

private theorem lower_upper_sum : (∑ i : Letter, lower q i * upper q i) = 0 := by
  simp only [lower_upper_same, Letter.sum_univ, TIndex.lowerSource, Bool.false_eq_true,
    reduceIte]
  exact six_four_zero q _ _

private theorem upper_lower_sum : (∑ i : Letter, upper q i * lower q i) = 0 := by
  simp only [upper_lower_same, Letter.sum_univ, TIndex.lowerTarget, Bool.false_eq_true,
    reduceIte]
  refine Eq.trans ?_ (six_four_zero q (upper q .e) (upper q .f))
  abel

theorem twistedCasimir_augmentation (H : kˣ) :
    AbsoluteBar.boundary k R 0 (twistedCasimir q H) = 0 := by
  simp only [twistedCasimir, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [map_add, map_sum, map_sum]
  simp only [AbsoluteBar.boundary_zero_tmul k R]
  simp only [CocycleData.twist_vector q H]
  simp only [TIndex.weight, TIndex.star, Bool.false_eq_true,
    reduceIte, pow_one, pow_zero, one_smul, Bool.not_true, Bool.not_false, vector]
  change (∑ i : Letter, ((H : k) • upper q i) * lower q i) +
    (∑ i : Letter, lower q i * upper q i) = 0
  simp only [Algebra.smul_mul_assoc, ← Finset.smul_sum, upper_lower_sum, lower_upper_sum,
    smul_zero, add_zero]

end ArExplicit.T

end

end OAI
