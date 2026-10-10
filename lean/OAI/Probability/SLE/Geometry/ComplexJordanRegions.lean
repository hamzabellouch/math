import OAI.Probability.SLE.Geometry.SchoenfliesInsideTransport

namespace OAI

/-! The bounded Jordan region in the complex coordinate chart. -/
noncomputable section
open Set

namespace SLEExactGauge

def complexInside (C : Set ℂ) : Set ℂ :=
  complexPlaneCoordinates ⁻¹' Schoenflies.inside (complexPlaneCoordinates '' C)

theorem complexInside_image (C : Set ℂ) :
    complexPlaneCoordinates '' complexInside C =
      Schoenflies.inside (complexPlaneCoordinates '' C) :=
  image_preimage_eq _ complexPlaneCoordinates.surjective

theorem complexInside_transport (h : ℂ ≃ₜ ℂ) (C : Set ℂ) :
    h '' complexInside C=complexInside (h '' C) := by
  let H := (complexPlaneCoordinates.symm.trans h).trans complexPlaneCoordinates
  have he : H '' (complexPlaneCoordinates '' C)=complexPlaneCoordinates '' (h '' C) := by
    ext x
    simp [H]
  apply complexPlaneCoordinates.injective.image_injective
  rw [complexInside_image]
  have hm : complexPlaneCoordinates '' (h '' complexInside C)=
      H '' (complexPlaneCoordinates '' complexInside C) := by
    ext x
    simp [H]
  rw [hm,complexInside_image,plane_homeomorph_inside,he]

theorem complexInside_eq_open {C U : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hb : Bornology.IsBounded U) (hfront : frontier U=C) : complexInside C=U := by
  apply complexPlaneCoordinates.injective.image_injective
  rw [complexInside_image]
  apply separating_inside_eq_open (Schoenflies.jordan_curve_theorem hC)
    (complexPlaneCoordinates.isOpen_image.mpr hU)
    (hconn.image _ complexPlaneCoordinates.continuous.continuousOn)
    (hne.image _) ?_ ?_
  · exact (hb.isCompact_closure.image complexPlaneCoordinates.continuous).isBounded.subset
      (image_mono subset_closure)
  · rw [← complexPlaneCoordinates.image_frontier,hfront]

theorem complexInside_closure {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C)) :
    closure (complexInside C)=complexInside C ∪ C := by
  apply complexPlaneCoordinates.injective.image_injective
  rw [complexPlaneCoordinates.image_closure,complexInside_image,image_union,
    complexInside_image]
  exact (Schoenflies.IsRegionOf.inside _).closure_eq
    (Schoenflies.jordan_curve_theorem hC)

end SLEExactGauge

end

end OAI
