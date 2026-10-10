import OAI.NumberTheory.DukePrimeDegree.Geometry.ShiftedRootWindowLeaf
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixMeasure

namespace OAI

/-! # The real marginal of an actual independent physical rectangle -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem rectangle_raw_realMarginal
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0) :
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    ∀ᵐ z ∂ρ, ((ρ.condKernel z.1).snd).map (Homeomorph.addRight (-z.2.2)) =
      (anchorNormalize (intrinsicRootLeaf q.distinct μ
        (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z))
        (Homeomorph.addRight (-z.2.2) '' J)).restrict (Homeomorph.addRight (-z.2.2) '' J) := by
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  intro ρ hp
  exact shifted_independent_window_root_leaf q.distinct A R hAR μ hfree σ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    (shiftedRootFactorPullback_map q.distinct A μ _
      (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding _
      (C.continuous_rectangleTime q g k Q).measurable (by rw [hA]))
    J hJ hwindow hp

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
