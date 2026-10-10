import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingFactorRebase
import OAI.NumberTheory.DukePrimeDegree.Geometry.RestrictedLeafProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedProductRectangle

namespace OAI

/-! # Local normalized products after rebasing a physical rectangle -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma normalized_product_map_factor (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (η : Measure ℝ)
    [SFinite ν] [SFinite η]
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (J : Set ℝ)
    (hV : MeasurableSet V) (hJ : MeasurableSet J) (hν0 : ν V ≠ 0) (hνt : ν V ≠ ⊤) :
    (((anchorNormalize ν V).restrict V).prod ((anchorNormalize η J).restrict J)).map
        q.remainingFactor =
      (anchorNormalize ((ν.prod η).map q.remainingFactor)
        (q.remainingFactor '' (V ×ˢ J))).restrict (q.remainingFactor '' (V ×ˢ J)) := by
  rw [anchorNormalize_prod_rectangle ν η V J hν0 hνt]
  let E := q.remainingFactor.toMeasurableEquiv
  have hEV : MeasurableSet (E '' (V ×ˢ J)) :=
    E.measurableEmbedding.measurableSet_image.mpr (hV.prod hJ)
  have hn := anchorNormalize_map_equiv (ν.prod η) E (V ×ˢ J)
  change ((anchorNormalize (ν.prod η) (V ×ˢ J)).restrict (V ×ˢ J)).map E =
    (anchorNormalize ((ν.prod η).map E) (E '' (V ×ˢ J))).restrict (E '' (V ×ˢ J))
  rw [hn,Measure.restrict_map E.measurable hEV,E.injective.preimage_image]

lemma independent_factor_rebase (d : ℕ) (q : InitialRootStep (d+1))
    (κ : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) [IsFiniteMeasure κ]
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (η : Measure ℝ)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (t : ℝ)
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hV : MeasurableSet V)
    (J : Set ℝ)
    (hp : κ = ((anchorNormalize
      ((ν.map (q.nextConjugation d (-t))).map (Homeomorph.mulLeft w)) V).restrict V).prod κ.snd)
    (hr : κ.snd.map (Homeomorph.addRight (-t)) =
      (anchorNormalize η (Homeomorph.addRight (-t) '' J)).restrict (Homeomorph.addRight (-t) '' J)) :
    (κ.map q.remainingFactor).map (Homeomorph.mulLeft (q.remainingFactor (w,t))⁻¹) =
      (((anchorNormalize ν (q.nextFactorRebase d w t '' V)).restrict (q.nextFactorRebase d w t '' V)).prod
        ((anchorNormalize η (Homeomorph.addRight (-t) '' J)).restrict
          (Homeomorph.addRight (-t) '' J))).map q.remainingFactor := by
  let ν₀ := (ν.map (q.nextConjugation d (-t))).map (Homeomorph.mulLeft w)
  let := anchorNormalize_restrict_finite_measure ν₀ V
  conv_lhs => rw [hp]
  rw [q.remainingFactor_product_rebase d,
    q.nextFactorRebase_reference_restrict d ν w t V hV,hr]

end InitialRootStep
end DukePrimeDegree

end

end OAI
