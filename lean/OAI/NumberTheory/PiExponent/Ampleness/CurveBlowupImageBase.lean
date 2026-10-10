import Mathlib
import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness
import OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem integral_scheme_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  let hred (U : Y.affineOpens) : _root_.IsReduced (Γ(Y,U.1) ⧸ f.ker.ideal U) := by
    rw [Scheme.Hom.ker_apply]
    exact isReduced_of_injective (RingHom.kerLift (f.app U.1).hom)
      (RingHom.kerLift_injective (f.app U.1).hom)
  let : ∀ U, AlgebraicGeometry.IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    change IsReduced (Spec (.of (Γ(Y,U.1) ⧸ f.ker.ideal U)))
    exact (affine_isReduced_iff _).mpr (hred U)
  let : IsReduced f.image := IsReduced.of_openCover f.image f.ker.subschemeCover.openCover
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image f.toImage
        f.toImage.continuous.continuousOn
  let : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponentSeshadri.Geometry

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {C X B : Scheme.{0}}

theorem toImage_isProper (f : C ⟶ X) [IsProper f] : IsProper f.toImage := by
  let : IsProper (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  exact IsProper.of_comp f.toImage f.imageι

theorem toImage_restrict_isIso (f : C ⟶ X) [IsProper f] [IsIntegral C]
    (U : X.Opens) [IsClosedImmersion (f ∣_ U)] :
    IsIso (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) := by
  let := integral_scheme_image f
  let : IsClosedImmersion
      ((f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) ≫ (f.imageι ∣_ U)) := by
    rw [← morphismRestrict_comp]
    exact Eq.mpr (congrArg (fun k : C ⟶ X => IsClosedImmersion (k ∣_ U))
      f.toImage_imageι) (inferInstance : IsClosedImmersion (f ∣_ U))
  let := IsClosedImmersion.of_comp_isClosedImmersion
    (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) (f.imageι ∣_ U)
  let : IsDominant (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsDominant f.toImage) _
  exact isIso_of_isClosedImmersion_of_surjective _

theorem restricted_curve_isClosedImmersion (π : B ⟶ X)
    (C : NumericalAmpleness.IntegralCurve B) (U : X.Opens) [IsIso (π ∣_ U)] :
    IsClosedImmersion ((C.embedding ≫ π) ∣_ U) := by
  rw [morphismRestrict_comp]
  exact IsClosedImmersion.comp (C.embedding ∣_ π ⁻¹ᵁ U) (π ∣_ U)

theorem genericPoint_eq_of_isDominant (f : C ⟶ X)
    [IsIntegral C] [IsIntegral X] [IsDominant f] :
    f (genericPoint C) = genericPoint X := by
  apply IsGenericPoint.eq _ (genericPoint_spec X)
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec C).image f.continuous

theorem stalkMap_isIso_of_restrict (f : C ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (x : C) (hx : f x ∈ U) : IsIso (f.stalkMap x) := by
  let q : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have hi : IsIso (((f ⁻¹ᵁ U).ι ≫ f).stalkMap q) := by
    rw [← morphismRestrict_ι]
    infer_instance
  rw [Scheme.Hom.stalkMap_comp] at hi
  change IsIso (f.stalkMap x ≫ (f ⁻¹ᵁ U).ι.stalkMap q) at hi
  have hq : IsIso ((f ⁻¹ᵁ U).ι.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp
      (inferInstance : IsOpenImmersion (f ⁻¹ᵁ U).ι)).2 q
  exact @IsIso.of_isIso_comp_right CommRingCat _ _ _ _
    (f.stalkMap x) ((f ⁻¹ᵁ U).ι.stalkMap q) hq hi

end PiExponent.CurveBlowupImage

end

end OAI
