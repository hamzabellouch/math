import OAI.Analysis.CircleDomains.Probability.NullLevelTuples

namespace OAI

/-! Null events on every pair of finite level-torus fibers are null for
the actual positive weighted tuple reference measure. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem tupleReference_product_null (ω : TupleType → ℝ≥0∞)
    (E : Set (LevelTuple × LevelTuple))
    (hE : ∀ i j : TupleType,
      ((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod
        (volume : Measure (Fin (j.1 + 1) → UnitAddCircle)))
        (Prod.map (tupleFiber i) (tupleFiber j) ⁻¹' E) = 0) :
    ((tupleReference ω).prod (tupleReference ω)) E = 0 := by
  rw [tupleReference, Measure.prod_sum, Measure.sum_apply_eq_zero]
  intro p
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.map_prod_map _ _ (measurable_tupleFiber _) (measurable_tupleFiber _),
    ((measurableEmbedding_tupleFiber _).prodMap
      (measurableEmbedding_tupleFiber _)).map_apply]
  rw [hE, mul_zero, mul_zero]

end CircleDomainRigidity

end

end OAI
