import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProjectiveEquality

namespace OAI

/-! # Normalized conditional restrictions on overlapping coordinate regions -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma anchorNormalize_restrict_inter {T : Type*} [MeasurableSpace T]
    (ν : Measure T) (U V : Set T) (hU : MeasurableSet U) :
    (anchorNormalize (ν.restrict V) U).restrict U =
      (anchorNormalize ν (U ∩ V)).restrict (U ∩ V) := by
  unfold anchorNormalize
  rw [Measure.restrict_apply hU,Measure.restrict_smul,Measure.restrict_restrict hU,
    Measure.restrict_smul]

lemma anchorNormalize_restrict_twice {T : Type*} [MeasurableSpace T]
    (ν : Measure T) (U V : Set T) (hU : MeasurableSet U)
    (hV0 : ν V ≠ 0) (hVT : ν V ≠ ∞) :
    (anchorNormalize ((anchorNormalize ν V).restrict V) U).restrict U =
      (anchorNormalize ν (U ∩ V)).restrict (U ∩ V) := by
  have he : (anchorNormalize ν V).restrict V = (ν V)⁻¹ • ν.restrict V :=
    Measure.restrict_smul _ _ _
  rw [he,anchorNormalize_smul _ _ _ (ENNReal.inv_ne_zero.mpr hVT)
    (ENNReal.inv_ne_top.mpr hV0)]
  exact anchorNormalize_restrict_inter ν U V hU

end DukePrimeDegree

end

end OAI
