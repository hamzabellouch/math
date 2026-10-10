import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCoordinateRestrictions

namespace OAI

/-! # Physical root rectangles represent the actual ambient measure -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

def physicalRootCoordinates {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) (z : T × (B × ℝ)) :
    RootSlice a b k × ℝ := (e (z.1,z.2.1),z.2.2 + τ (z.1,z.2.1))

lemma physicalRootCoordinates_embedding {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ) :
    MeasurableEmbedding (physicalRootCoordinates e τ) :=
  (shiftedRootFactorCoordinateMap_embedding e he τ hτ).comp
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding

def physicalRootParam {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) : T × (B × ℝ) → X n :=
  rootQuotientParametrization hab ∘ physicalRootCoordinates e τ

lemma map_physicalRootCoordinates {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcover : A.transverse ⊆ Set.range e) :
    (shiftedRootFactorPullback hab A μ e τ).map (physicalRootCoordinates e τ) =
      A.coordinateMeasure μ := by
  have H := shiftedRootFactorPullback_map hab A μ e he τ hτ hcover
  rw [Measure.map_map (shiftedRootFactorCoordinateMap_embedding e he τ hτ).measurable
    MeasurableEquiv.prodAssoc.symm.measurable] at H
  exact H.symm

theorem map_physical_root_rectangle {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcover : A.transverse ⊆ Set.range e)
    (D : Set (T × (B × ℝ))) (hD : MeasurableSet D)
    (hDA : physicalRootCoordinates e τ '' D ⊆ A.domain) :
    ((shiftedRootFactorPullback hab A μ e τ).restrict D).map (physicalRootParam hab e τ) =
      μ.restrict (physicalRootParam hab e τ '' D) := by
  let F := physicalRootCoordinates e τ
  have hF := physicalRootCoordinates_embedding e he τ hτ
  have H := hF.restrict_map (shiftedRootFactorPullback hab A μ e τ) (F '' D)
  rw [hF.injective.preimage_image,map_physicalRootCoordinates hab A μ e he τ hτ hcover] at H
  calc
    _ = (((shiftedRootFactorPullback hab A μ e τ).restrict D).map F).map
        (rootQuotientParametrization hab) := by
      rw [Measure.map_map (rootQuotientParametrization_localHomeomorph hab).continuous.measurable
        hF.measurable]
      rfl
    _ = ((A.coordinateMeasure μ).restrict (F '' D)).map (rootQuotientParametrization hab) := by
      rw [←H]
    _ = μ.restrict (rootQuotientParametrization hab '' (F '' D)) :=
      RootBox.map_restricted_coordinates A μ (F '' D) (hF.measurableSet_image.mpr hD) hDA
    _ = _ := by rw [Set.image_image]; rfl

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {S : Type*} [TopologicalSpace S]
  (C : RootPrefixCoordinates n q.processed S) (g : G n) (k : Fin n)

lemma rectangle_physicalParam (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z =
      rightAction (Quotient.mk _ ((g * z.1.val.1.val) * C.base z.1.val.2))
        (z.2.1.val.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2) := by
  change rootQuotientParametrization q.distinct
    (C.rectangleSlice q g k Q (z.1,z.2.1),z.2.2 + C.rectangleTime q g k Q (z.1,z.2.1)) = _
  rw [C.rectangleSlice_orbit q g k Q,add_sub_cancel_right]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
