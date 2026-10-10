import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Ruled.ProjectionDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

def perpendicularProjectionEquiv {h : ℝ} (hh : 0 < h) (g : Plane) :
    Plane ≃L[ℝ] ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) :=
  (LinearEquiv.ofBijective (perpendicularProjection h g)
    ⟨perpendicularProjection_injective hh g,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        simp only [finrank_euclideanSpace_fin,
          perpendicularPlane_finrank _ (physicalUnit_norm h g)])).mp
        (perpendicularProjection_injective hh g)⟩).toContinuousLinearEquiv

@[simp] theorem perpendicularProjectionEquiv_apply {h : ℝ} (hh : 0 < h)
    (g p : Plane) : perpendicularProjectionEquiv hh g p = perpendicularProjection h g p := rfl

lemma projectedCylinder_base_measurable {h : ℝ} (hh : 0 < h) (g : Plane)
    {T : Set Plane} (hT : MeasurableSet T) :
    MeasurableSet (projectedCylinder h g T).base := by
  exact (perpendicularProjectionEquiv hh g).toHomeomorph.measurableEmbedding.measurableSet_image.mpr hT

lemma projectedCylinder_base_bounded {h : ℝ} (hh : 0 < h) (g : Plane)
    {T : Set Plane} (hT : Bornology.IsBounded T) :
    Bornology.IsBounded (projectedCylinder h g T).base := by
  exact (perpendicularProjectionEquiv hh g).toContinuousLinearMap.lipschitzWith.isBounded_image hT

lemma projectedCylinder_base_open {h : ℝ} (hh : 0 < h) (g : Plane)
    {T : Set Plane} (hT : IsOpen T) : IsOpen (projectedCylinder h g T).base := by
  exact (perpendicularProjectionEquiv hh g).isOpenMap T hT

lemma projectedCylinder_base_compact {h : ℝ} (hh : 0 < h) (g : Plane)
    {T : Set Plane} (hT : IsCompact T) : IsCompact (projectedCylinder h g T).base := by
  exact hT.image (perpendicularProjectionEquiv hh g).continuous

def Cylinder.transport (C : Cylinder) (F : Space ≃ᵢ Space) : Cylinder :=
  (C.rotate F.toRealLinearIsometryEquiv).translate (F 0)

lemma Cylinder.transport_carrier (C : Cylinder) (F : Space ≃ᵢ Space) :
    (C.transport F).carrier = F '' C.carrier := by
  rw [Cylinder.transport, Cylinder.translate_carrier, Cylinder.rotate_carrier, ← image_comp]
  congr 1
  funext x
  simp [IsometryEquiv.toRealLinearIsometryEquiv_apply]

lemma Cylinder.transport_area (C : Cylinder) (F : Space ≃ᵢ Space) :
    (C.transport F).area = C.area := by
  rw [Cylinder.transport, Cylinder.translate_area, Cylinder.rotate_area]

lemma Cylinder.transport_parallelogram {C : Cylinder} (hC : C.parallelogram)
    (F : Space ≃ᵢ Space) : (C.transport F).parallelogram :=
  Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram hC F.toRealLinearIsometryEquiv) (F 0)

def Cylinder.transportBase (C : Cylinder) (F : Space ≃ᵢ Space) :
    ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) ≃ᵢ
      ((Submodule.span ℝ ({(C.transport F).axis} : Set Space))ᗮ) :=
  (rotatedPlane C.axis F.toRealLinearIsometryEquiv).toIsometryEquiv.trans
    (IsometryEquiv.addLeft ((C.rotate F.toRealLinearIsometryEquiv).transversePart (F 0)))

lemma Cylinder.transport_base (C : Cylinder) (F : Space ≃ᵢ Space) :
    (C.transport F).base = C.transportBase F '' C.base := by
  simp only [Cylinder.transport, Cylinder.translate, Cylinder.rotate,
    Cylinder.transportBase, Set.image_image]
  rfl

lemma Cylinder.transport_measurable {C : Cylinder} (hC : MeasurableSet C.base)
    (F : Space ≃ᵢ Space) : MeasurableSet (C.transport F).base := by
  rw [Cylinder.transport_base]
  exact (C.transportBase F).toHomeomorph.measurableEmbedding.measurableSet_image.mpr hC

lemma Cylinder.transport_bounded {C : Cylinder} (hC : Bornology.IsBounded C.base)
    (F : Space ≃ᵢ Space) : Bornology.IsBounded (C.transport F).base := by
  rw [Cylinder.transport_base]
  exact (C.transportBase F).isometry.lipschitzWith.isBounded_image hC

lemma Cylinder.transport_open {C : Cylinder} (hC : IsOpen C.base)
    (F : Space ≃ᵢ Space) : IsOpen (C.transport F).base := by
  rw [Cylinder.transport_base]
  exact (C.transportBase F).toHomeomorph.isOpenMap _ hC

lemma Cylinder.transport_compact {C : Cylinder} (hC : IsCompact C.base)
    (F : Space ≃ᵢ Space) : IsCompact (C.transport F).base := by
  rw [Cylinder.transport_base]
  exact hC.image (C.transportBase F).continuous

theorem physicalProjection_proof : PhysicalProjectionStatement := by
  intro h T g hh hTb hTm F
  refine ⟨(projectedCylinder h g T).transport F, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Cylinder.transport_carrier, projectedCylinder_carrier]
  · rfl
  · rw [Cylinder.transport_area, projectedCylinder_area hh]
  · exact Cylinder.transport_measurable (projectedCylinder_base_measurable hh g hTm) F
  · exact Cylinder.transport_bounded (projectedCylinder_base_bounded hh g hTb) F
  · exact (Cylinder.transport_bounded (projectedCylinder_base_bounded hh g hTb) F).measure_lt_top
  · intro hT
    exact Cylinder.transport_open (projectedCylinder_base_open hh g hT) F
  · intro hT
    exact Cylinder.transport_compact (projectedCylinder_base_compact hh g hT) F
  · intro hT
    exact Cylinder.transport_parallelogram (projectedCylinder_parallelogram hh g hT) F

end RuledApproximation

end

end OAI
