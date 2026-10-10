import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal

namespace OAI

namespace PiExponent.SectionImageSupport
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal

variable {X : Scheme.{0}} {M : X.Modules}

lemma isoOpen_preimage_on_frame (φ : M ⟶ structureSheaf X) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    U.ι ⁻¹ᵁ SectionOpens.isoOpen φ = U.toScheme.basicOpen
      (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom)) := by
  rw [← SectionOpens.isoOpen_restrict φ U.ι]
  let ψ := (Scheme.Modules.restrictFunctor U.ι).map φ
  calc
    SectionOpens.isoOpen ψ = SectionOpens.isoOpen
        (ψ ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) :=
      (SectionOpens.isoOpen_postcomp ψ (Scheme.Modules.restrictUnitIso U.ι)).symm
    _ = SectionOpens.isoOpen (e.inv ≫ ψ ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) :=
      (SectionOpens.isoOpen_precomp e.symm _).symm
    _ = _ := by
      simpa only [coefficient, Iso.refl_hom, Category.comp_id] using!
        (isoOpen_eq_basicOpen (Iso.refl (O U.toScheme))
          (e.inv ≫ ψ ≫ (Scheme.Modules.restrictUnitIso U.ι).hom))

lemma preimage_basicOpen_topIso_hom (U : X.Opens) (a : Γ(U.toScheme,⊤)) :
    U.ι ⁻¹ᵁ X.basicOpen (U.topIso.hom a) = U.toScheme.basicOpen a := by
  rw [← U.ι_image_basicOpen_topIso_inv (U.topIso.hom a), U.ι.preimage_image_eq]
  rw [Iso.hom_inv_id_apply]

theorem imageIdealSheaf_support (L : LineBundle X)
    (φ : L.sheaf ⟶ structureSheaf X) :
    letI := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
    letI : SheafOfModules.IsQuasicoherent L.sheaf :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose.isQuasicoherent
    ((imageIdealSheaf φ).support : Set X) = (SectionOpens.isoOpen φ : Set X)ᶜ := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  let : SheafOfModules.IsQuasicoherent L.sheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose.isQuasicoherent
  ext x
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let A : X.affineOpens := ⟨W, hW⟩
  let e : L.sheaf.restrict W.ι ≅ structureSheaf W.toScheme := restrictOpenFrame hWV eV
  change x ∈ (imageIdealSheaf φ).support ↔ x ∉ SectionOpens.isoOpen φ
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) hxW,
    imageIdealSheaf_on_frame φ A e, X.zeroLocus_span, X.zeroLocus_singleton]
  apply not_congr
  change (⟨x, hxW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ X.basicOpen
      (W.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor W.ι).map φ ≫
        (Scheme.Modules.restrictUnitIso W.ι).hom))) ↔
    (⟨x, hxW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ SectionOpens.isoOpen φ
  rw [preimage_basicOpen_topIso_hom, isoOpen_preimage_on_frame φ W e]

end
end PiExponent.SectionImageSupport

end OAI
