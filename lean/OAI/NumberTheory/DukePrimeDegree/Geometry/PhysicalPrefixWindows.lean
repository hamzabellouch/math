import OAI.NumberTheory.DukePrimeDegree.Geometry.LargePhysicalRectangles

namespace OAI

/-! # Physical product windows covering compact prefix-time sets -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

structure PhysicalPrefixWindow {d : ℕ} (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) where
  pivot : Fin (d+1)
  rectangle : RootTransverseRectangle (C.factorPivotDomain q g pivot)
  second_nonempty : rectangle.second.Nonempty
  box : RootBox q.distinct pivot
  transverse_eq : box.transverse = range (C.rectangleSlice q g pivot rectangle)
  interval : Set ℝ
  interval_open : IsOpen interval
  radius : ℝ
  box_time_bound : box.time ⊆ rootLeafWindow radius 0
  second_bound : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))
  second_bound_compact : IsCompact second_bound
  second_subset : rectangle.second ⊆ second_bound
  interval_bound : Set ℝ
  interval_bound_compact : IsCompact interval_bound
  interval_subset : interval ⊆ interval_bound
  window : ∀ w : rectangle.first × rectangle.second,
    (Homeomorph.addRight (C.rectangleTime q g pivot rectangle w)) '' interval ⊆ box.time

namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*} [TopologicalSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}

def toBox (B : PhysicalPrefixWindow q C g)
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) : RootPrefixBox C c q.initial hf g :=
  C.physicalPrefixBox q c hf g B.pivot B.rectangle B.box B.transverse_eq
    B.interval B.interval_open B.window

variable [MeasurableSpace T] [BorelSpace T]

theorem independent (B : PhysicalPrefixWindow q C g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    letI : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
    haveI : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct B.box μ
      (C.rectangleSlice q g B.pivot B.rectangle) (C.rectangleTime q g B.pivot B.rectangle)
    haveI := shiftedRootFactorPullback_finite q.distinct B.box μ
      (C.rectangleSlice q g B.pivot B.rectangle)
      (C.rectangleSlice_isOpenEmbedding q g B.pivot B.rectangle).measurableEmbedding
      (C.rectangleTime q g B.pivot B.rectangle)
      (C.continuous_rectangleTime q g B.pivot B.rectangle).measurable
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ B.interval))
    ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  let : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
  let : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct B.box μ
    (C.rectangleSlice q g B.pivot B.rectangle)
    (C.rectangleSlice_isOpenEmbedding q g B.pivot B.rectangle).measurableEmbedding
    (C.rectangleTime q g B.pivot B.rectangle)
    (C.continuous_rectangleTime q g B.pivot B.rectangle).measurable
  apply conditional_restrict_rectangle_product σ B.interval B.interval_open.measurableSet
  exact remainingRootBox_conditional_product d q C g B.pivot B.rectangle B.box B.radius
    B.box_time_bound (by rw [B.transverse_eq]) B.interval B.interval_open.measurableSet
    B.window μ hA

end PhysicalPrefixWindow

namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

theorem exists_physicalPrefixWindow_covering (s : UpperRootTransverse (d+1) × T)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1)
    (K : Set c.Time) (hK : IsCompact K) :
    ∃ B : PhysicalPrefixWindow q C g,
      s ∈ B.rectangle.first ∧ K ⊆ (B.toBox c hf).time := by
  let E := remainingFactorTime q c hf
  let P := E.symm '' K
  have hP : IsCompact P := hK.image E.symm.continuous
  let V := (Prod.fst '' P) ∪ {1}
  let I := (Prod.snd '' P) ∪ {0}
  have hV : IsCompact V := (hP.image continuous_fst).union isCompact_singleton
  have hI : IsCompact I := (hP.image continuous_snd).union isCompact_singleton
  obtain ⟨k,hk⟩ := exists_rootPivot q.root.1 ((g*s.1.val)*C.base s.2)
  obtain ⟨Q,A,R,J,V',I',hJ,hsQ,hVQ,hIJ,hV',hQV',hI',hJI',hA,hAR,hw⟩ :=
    C.exists_large_physical_rectangle q g k s hk hfree V hV I hI ⟨0,Or.inr rfl⟩
  let B : PhysicalPrefixWindow q C g :=
    ⟨k,Q,⟨1,hVQ (Or.inr rfl)⟩,A,hA,J,hJ,R,hAR,V',hV',hQV',I',hI',hJI',hw⟩
  refine ⟨B,hsQ,?_⟩
  intro t ht
  refine ⟨E.symm t,⟨hVQ (Or.inl ?_),hIJ (Or.inl ?_)⟩,E.apply_symm_apply t⟩
  · exact ⟨E.symm t,⟨t,ht,rfl⟩,rfl⟩
  · exact ⟨E.symm t,⟨t,ht,rfl⟩,rfl⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
