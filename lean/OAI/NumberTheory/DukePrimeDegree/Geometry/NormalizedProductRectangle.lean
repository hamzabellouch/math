import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedIntersections

namespace OAI

/-! # Normalizing an actual product on a measurable rectangle -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma anchorNormalize_restrict_finite_measure
    {A : Type*} [MeasurableSpace A] (ν : Measure A) (V : Set A) :
    IsFiniteMeasure ((anchorNormalize ν V).restrict V) := by
  constructor
  change ((ν V)⁻¹ • ν).restrict V univ < ⊤
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.smul_apply,smul_eq_mul]
  exact (ENNReal.inv_mul_le_one (ν V)).trans_lt ENNReal.one_lt_top

theorem anchorNormalize_prod_rectangle
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (η : Measure B) [SFinite ν] [SFinite η]
    (V : Set A) (J : Set B)
    (hν0 : ν V ≠ 0) (hνt : ν V ≠ ⊤) :
    ((anchorNormalize ν V).restrict V).prod ((anchorNormalize η J).restrict J) =
      (anchorNormalize (ν.prod η) (V ×ˢ J)).restrict (V ×ˢ J) := by
  unfold anchorNormalize
  rw [Measure.restrict_smul,Measure.restrict_smul,Measure.prod_smul_left,
    Measure.prod_smul_right,smul_smul,Measure.prod_restrict,Measure.restrict_smul,
    Measure.prod_prod,ENNReal.mul_inv (Or.inl hν0) (Or.inl hνt)]

end DukePrimeDegree

end

end OAI
