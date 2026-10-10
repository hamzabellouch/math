import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedFactorProduct

namespace OAI

/-! # Finite rectangle normalization, including null rectangles -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem anchorNormalize_prod_rectangle_of_finite
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (η : Measure B) [SFinite ν] [SFinite η]
    (V : Set A) (J : Set B) (hνt : ν V ≠ ⊤) :
    ((anchorNormalize ν V).restrict V).prod ((anchorNormalize η J).restrict J) =
      (anchorNormalize (ν.prod η) (V ×ˢ J)).restrict (V ×ˢ J) := by
  by_cases hν0 : ν V = 0
  · have h0 : ν.restrict V = 0 := Measure.restrict_eq_zero.mpr hν0
    have hp0 : (ν.prod η).restrict (V ×ˢ J) = 0 :=
      Measure.restrict_eq_zero.mpr (by rw [Measure.prod_prod,hν0,zero_mul])
    simp [anchorNormalize,Measure.restrict_smul,h0,hp0]
  · exact anchorNormalize_prod_rectangle ν η V J hν0 hνt

namespace InitialRootStep

lemma normalized_product_map_factor_of_finite (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (η : Measure ℝ)
    [SFinite ν] [SFinite η]
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (J : Set ℝ)
    (hV : MeasurableSet V) (hJ : MeasurableSet J) (hνt : ν V ≠ ⊤) :
    (((anchorNormalize ν V).restrict V).prod ((anchorNormalize η J).restrict J)).map
        q.remainingFactor =
      (anchorNormalize ((ν.prod η).map q.remainingFactor)
        (q.remainingFactor '' (V ×ˢ J))).restrict (q.remainingFactor '' (V ×ˢ J)) := by
  by_cases hν0 : ν V = 0
  · have h0 : ν.restrict V = 0 := Measure.restrict_eq_zero.mpr hν0
    have hprod : ((ν.prod η).map q.remainingFactor) (q.remainingFactor '' (V ×ˢ J)) = 0 := by
      rw [Measure.map_apply q.remainingFactor.measurable
        (q.remainingFactor.measurableEmbedding.measurableSet_image.mpr (hV.prod hJ)),
        q.remainingFactor.injective.preimage_image,Measure.prod_prod,hν0,zero_mul]
    have hp0 : ((ν.prod η).map q.remainingFactor).restrict
        (q.remainingFactor '' (V ×ˢ J)) = 0 := Measure.restrict_eq_zero.mpr hprod
    simp [anchorNormalize,Measure.restrict_smul,h0,hp0]
  · exact q.normalized_product_map_factor d ν η V J hV hJ hν0 hνt

end InitialRootStep
end DukePrimeDegree

end

end OAI
