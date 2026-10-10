import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalRectangleProducts
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRootEmbeddings

namespace OAI

/-! # Independent rectangles with their actual quotient embeddings

The rectangle carries both its product conditional law and the geometric
inclusions that identify its measure with an ambient restriction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_remainingRoot_physical_independent_box
    (d : ℕ) (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    (z : C.factorPivotDomain q g k) (t : ℝ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ Q : RootTransverseRectangle (C.factorPivotDomain q g k), ∃ hQ : Nonempty Q.second,
      letI := hQ
      haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
      ∃ (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ),
        IsOpen J ∧ z.val ∈ Q.first ×ˢ Q.second ∧ t ∈ J ∧
        A.time ⊆ rootLeafWindow R 0 ∧
        A.transverse = Set.range (C.rectangleSlice q g k Q) ∧
        (∀ w : Q.first × Q.second,
          (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) ∧
        let σ := shiftedRootFactorPullback q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
        haveI := shiftedRootFactorPullback_finite q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
          (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
        let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
        ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  obtain ⟨Q,A,R,J,hJ,hz,ht,hcover,hbound,hw⟩ := exists_shifted_root_rectangle
    (C.factorPivotDomain_open q g k) q.distinct (C.factorSlice q g k)
    (C.factorSlice_isOpenEmbedding q g k) (C.factorTime q g k)
    (C.continuous_factorTime q g k) z t
  let : Nonempty Q.second := ⟨⟨z.val.2,hz.2⟩⟩
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  refine ⟨Q,inferInstance,A,R,J,hJ,hz,ht,hbound,hcover,hw,?_⟩
  let σ := shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  apply conditional_restrict_rectangle_product σ J hJ.measurableSet
  exact remainingRootBox_conditional_product d q C g k Q A R hbound
    (by rw [hcover]; exact subset_rfl) J hJ.measurableSet hw μ hA

end DukePrimeDegree

end

end OAI
