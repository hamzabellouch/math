import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRootRectangles

namespace OAI

/-! # Quotient embeddings of physical root rectangles -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [TopologicalSpace T] [TopologicalSpace B]

omit [MeasurableSpace T] [MeasurableSpace B] in
lemma physicalRootCoordinates_isOpenEmbedding {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : T × B → ℝ) (hτ : Continuous τ) :
    Topology.IsOpenEmbedding (physicalRootCoordinates e τ) := by
  exact (he.prodMap (Topology.IsOpenEmbedding.id (X := ℝ))).comp
    ((fiberShear (Homeomorph.refl (T × B)) τ hτ).isOpenEmbedding.comp
      (Homeomorph.prodAssoc T B ℝ).symm.isOpenEmbedding)

omit [MeasurableSpace T] [MeasurableSpace B] in
theorem physicalRootParam_isOpenEmbedding {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k)
    (e : T × B → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : T × B → ℝ) (hτ : Continuous τ)
    (D : Set (T × (B × ℝ))) (hD : IsOpen D)
    (hDA : physicalRootCoordinates e τ '' D ⊆ A.domain) :
    Topology.IsOpenEmbedding (D.domRestrict (physicalRootParam hab e τ)) := by
  let F : D → A.domain := fun z =>
    ⟨physicalRootCoordinates e τ z.val,hDA ⟨z.val,z.prop,rfl⟩⟩
  have hF : Topology.IsOpenEmbedding F := by
    apply Topology.IsOpenEmbedding.of_comp F
      (A.transverse_open.prod A.time_open).isOpenEmbedding_subtypeVal
    exact (physicalRootCoordinates_isOpenEmbedding e he τ hτ).comp hD.isOpenEmbedding_subtypeVal
  exact A.embedding.comp hF

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {S : Type*} [TopologicalSpace S]
  (C : RootPrefixCoordinates n q.processed S) (g : G n) (k : Fin n)

lemma rectangle_coordinates_inside
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    physicalRootCoordinates (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) ''
      (univ ×ˢ (univ ×ˢ J)) ⊆ A.domain := by
  rintro _ ⟨z,hz,rfl⟩
  constructor
  · rw [hA]
    exact ⟨(z.1,z.2.1),rfl⟩
  · exact hwindow (z.1,z.2.1) ⟨z.2.2,hz.2.2,rfl⟩

theorem rectangle_param_isOpenEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    Topology.IsOpenEmbedding ((univ ×ˢ (univ ×ˢ J)).domRestrict
      (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q))) :=
  physicalRootParam_isOpenEmbedding q.distinct A _ (C.rectangleSlice_isOpenEmbedding q g k Q)
    _ (C.continuous_rectangleTime q g k Q) _ (isOpen_univ.prod (isOpen_univ.prod hJ))
    (C.rectangle_coordinates_inside q g k Q A hA J hwindow)

variable [MeasurableSpace S] [BorelSpace S]

theorem rectangle_measure_map
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X n)) :
    ((shiftedRootFactorPullback q.distinct A μ (C.rectangleSlice q g k Q)
      (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))).map
      (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)) =
        μ.restrict (physicalRootParam q.distinct (C.rectangleSlice q g k Q)
          (C.rectangleTime q g k Q) '' (univ ×ˢ (univ ×ˢ J))) :=
  map_physical_root_rectangle q.distinct A μ _
    (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding _
    (C.continuous_rectangleTime q g k Q).measurable
    (by rw [hA]) _ (MeasurableSet.univ.prod (MeasurableSet.univ.prod hJ))
    (C.rectangle_coordinates_inside q g k Q A hA J hwindow)

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
