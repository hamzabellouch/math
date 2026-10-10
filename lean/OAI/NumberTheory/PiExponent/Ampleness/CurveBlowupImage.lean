import OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement
import OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus
import OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension
import OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {X B : Scheme.{0}}

def imageCurve (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    NumericalAmpleness.IntegralCurve X :=
  let f := C.embedding ≫ π
  letI := integral_scheme_image f
  { scheme := f.image
    embedding := f.imageι
    closedImmersion := inferInstance
    integral := inferInstance
    dimension := CurveProperImageDimension.image_dimension_eq_one_of_nonconstant
      f C.dimension hn }

def imageMap (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    C.scheme ⟶ (imageCurve π C hn).scheme := (C.embedding ≫ π).toImage

@[simp] theorem imageMap_comp (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    imageMap π C hn ≫ (imageCurve π C hn).embedding = C.embedding ≫ π :=
  (C.embedding ≫ π).toImage_imageι

instance imageMap_isProper (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    IsProper (imageMap π C hn) := toImage_isProper _

instance imageMap_isDominant (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    IsDominant (imageMap π C hn) := by
  change IsDominant (C.embedding ≫ π).toImage
  infer_instance

theorem imageMap_isFinite (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B) [NoetherianSpace C.scheme]
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    IsFinite (imageMap π C hn) := by
  let : Nontrivial (imageCurve π C hn).scheme :=
    CurveProperImageDimension.image_nontrivial_of_nonconstant (C.embedding ≫ π) hn
  exact CurveMorphismFinite.isFinite_of_proper_dominant (imageMap π C hn) C.dimension.le

theorem imageMap_restrict_isIso (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)] :
    IsIso (imageMap π C hn ∣_ ((imageCurve π C hn).embedding ⁻¹ᵁ U)) := by
  let := restricted_curve_isClosedImmersion π C U
  exact toImage_restrict_isIso (C.embedding ≫ π) U

theorem imageMap_preimage_nonempty (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    Nonempty (imageMap π C hn ⁻¹ᵁ ((imageCurve π C hn).embedding ⁻¹ᵁ U)) := by
  obtain ⟨c, hc⟩ := hU
  refine ⟨⟨c, ?_⟩⟩
  change (imageCurve π C hn).embedding (imageMap π C hn c) ∈ U
  simpa only [← Scheme.Hom.comp_apply, imageMap_comp] using hc

def imageFunctionFieldIso (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)]
    (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    (imageCurve π C hn).scheme.functionField ≅ C.scheme.functionField :=
  letI := imageMap_restrict_isIso π C hn U
  functionFieldIso (imageMap π C hn) ((imageCurve π C hn).embedding ⁻¹ᵁ U)
    (imageMap_preimage_nonempty π C hn U hU)

theorem imageFunctionFieldIso_generic (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)]
    (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    Spec.map (imageFunctionFieldIso π C hn U hU).hom ≫
      (imageCurve π C hn).scheme.fromSpecStalk
        (genericPoint (imageCurve π C hn).scheme) ≫
      (imageCurve π C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ π := by
  have h := functionFieldMap_fromSpecStalk (imageMap π C hn)
  change Spec.map (functionFieldMap (imageMap π C hn)) ≫ _ ≫ _ = _
  rw [← Category.assoc, h, Category.assoc, imageMap_comp]

theorem blowup_restrict_isIso {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : IsIso (π ∣_ I.support.compl) := by
  apply (hπ.morphismRestrict I.support.compl).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end PiExponent.CurveBlowupImage

end

end OAI
