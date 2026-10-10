import OAI.NumberTheory.DukePrimeDegree.Geometry.RootRectangleMeasures

namespace OAI

/-! # Common sampled references in actual quotient rectangles -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem rectangle_common_reference
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k)
    (hcover : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (P : X (d+1) → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let ρ := (shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    let σ := ρ.map (q.includeRootRectangle d Subtype.val)
    ∀ᵐ s ∂σ.fst, ∃ w : positiveRootGeneratedGroup (q.remaining.erase q.root), ∃ t₀ : ℝ,
      P (q.rootFiberPoint d (C.rectangleBasePoint q g k Q) (s,(w,t₀))) ∧
      ∀ᵐ t ∂(σ.condKernel s).snd,
        P (q.rootFiberPoint d (C.rectangleBasePoint q g k Q) (s,(w,t))) ∧
        q.nextIntrinsicProduct d μ (q.rootFiberPoint d (C.rectangleBasePoint q g k Q) (s,(w,t))) =
          q.nextIntrinsicProduct d μ (q.rootFiberPoint d (C.rectangleBasePoint q g k Q) (s,(w,t₀))) := by
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  intro ρ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  intro hprod σ
  have hb := (C.continuous_rectangleBasePoint q g k Q).measurable
  have hmap := C.map_included_rectangle q g k Q A hcover J hJ hwindow μ
  have hdom : σ.map (q.rootFiberPoint d (C.rectangleBasePoint q g k Q)) ≪ μ := by
    rw [hmap]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hp : ∀ᵐ z ∂σ, P (q.rootFiberPoint d (C.rectangleBasePoint q g k Q) z) :=
    ae_of_ae_map (q.measurable_rootFiberPoint d _ hb).aemeasurable (hdom.ae_le hP)
  exact q.exists_common_nextProduct_reference d μ hA _ hb σ hdom
    (q.includeRootRectangle_conditional_independent d Subtype.val measurable_subtype_coe ρ hprod)
    (fun z => P (q.rootFiberPoint d (C.rectangleBasePoint q g k Q) z)) hp

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
