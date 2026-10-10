import OAI.NumberTheory.DukePrimeDegree.Geometry.CompactPhysicalRectangles
import OAI.NumberTheory.DukePrimeDegree.Geometry.FactorSliceFreeness
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixBox
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalIndependentBoxes

namespace OAI

/-! # Bounded independent physical rectangles covering arbitrary compact fibers -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem exists_large_physical_rectangle (s : UpperRootTransverse (d+1) × T)
    (hs : ((g*s.1.val)*C.base s.2).val k q.root.1 ≠ 0)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1)
    (K : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hK : IsCompact K)
    (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty) :
    ∃ (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
      (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ)
      (K' : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (I' : Set ℝ),
      IsOpen J ∧ s ∈ Q.first ∧ K ⊆ Q.second ∧ I ⊆ J ∧
      IsCompact K' ∧ Q.second ⊆ K' ∧ IsCompact I' ∧ J ⊆ I' ∧
      A.transverse = range (C.rectangleSlice q g k Q) ∧
      A.time ⊆ rootLeafWindow R 0 ∧
      ∀ w : Q.first × Q.second,
        (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time := by
  let E := q.nextGroupCoordinates
  obtain ⟨r,hr⟩ := (hK.image E.continuous).isBounded.subset_ball 0
  let V := E ⁻¹' Metric.ball 0 r
  let K' := E.symm '' Metric.closedBall 0 r
  have hV : IsOpen V := Metric.isOpen_ball.preimage E.continuous
  have hKV : K ⊆ V := fun w hw => hr ⟨w,hw,rfl⟩
  have hK' : IsCompact K' := (isCompact_closedBall 0 r).image E.symm.continuous
  have hVK' : V ⊆ K' := by
    intro w hw
    exact ⟨E w,Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le,E.symm_apply_apply w⟩
  obtain ⟨rI,hrI⟩ := hI.isBounded.subset_ball 0
  obtain ⟨Q,A,R,J,hJ,hsQ,hKQ,hIJ,hQV,hJI,hA,hAR,hw⟩ :=
    exists_shifted_root_rectangle_covering_compact (C.factorPivotDomain_open q g k)
      q.distinct (C.factorSlice q g k) (C.factorSlice_isOpenEmbedding q g k)
      (C.factorTime q g k) (C.continuous_factorTime q g k) s
      (C.factorPivotDomain_cylinder q g k s hs)
      (C.factorSlice_fiber_injective_of_free q g k s hfree)
      K hK I hI hne V hV hKV (Metric.ball 0 rI) Metric.isOpen_ball hrI
  exact ⟨Q,A,R,J,K',Metric.closedBall 0 rI,hJ,hsQ,hKQ,hIJ,hK',
    hQV.trans hVK',isCompact_closedBall 0 rI,hJI.trans Metric.ball_subset_closedBall,
    hA,hAR,hw⟩

variable [MeasurableSpace T] [BorelSpace T]

theorem exists_large_independent_physical_rectangle (s : UpperRootTransverse (d+1) × T)
    (hs : ((g*s.1.val)*C.base s.2).val k q.root.1 ≠ 0)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1)
    (K : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hK : IsCompact K)
    (hKne : K.Nonempty) (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hAinv : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ Q : RootTransverseRectangle (C.factorPivotDomain q g k), ∃ hQ : Nonempty Q.second,
      letI := hQ
      haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
      ∃ (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ)
        (K' : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (I' : Set ℝ),
        IsOpen J ∧ s ∈ Q.first ∧ K ⊆ Q.second ∧ I ⊆ J ∧
        IsCompact K' ∧ Q.second ⊆ K' ∧ IsCompact I' ∧ J ⊆ I' ∧
        A.transverse = range (C.rectangleSlice q g k Q) ∧
        A.time ⊆ rootLeafWindow R 0 ∧
        (∀ w : Q.first × Q.second,
          (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) ∧
        let σ := shiftedRootFactorPullback q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
        haveI := shiftedRootFactorPullback_finite q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
          (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
        let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
        ∀ᵐ a ∂ρ.fst, ρ.condKernel a = (ρ.condKernel a).fst.prod (ρ.condKernel a).snd := by
  obtain ⟨Q,A,R,J,K',I',hJ,hsQ,hKQ,hIJ,hK',hQK',hI',hJI',hA,hAR,hw⟩ :=
    C.exists_large_physical_rectangle q g k s hs hfree K hK I hI hne
  obtain ⟨w,hwK⟩ := hKne
  let : Nonempty Q.second := ⟨⟨w,hKQ hwK⟩⟩
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  refine ⟨Q,inferInstance,A,R,J,K',I',hJ,hsQ,hKQ,hIJ,hK',hQK',hI',hJI',hA,hAR,hw,?_⟩
  let σ := shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  apply conditional_restrict_rectangle_product σ J hJ.measurableSet
  exact remainingRootBox_conditional_product d q C g k Q A R hAR (by rw [hA])
    J hJ.measurableSet hw μ hAinv

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
