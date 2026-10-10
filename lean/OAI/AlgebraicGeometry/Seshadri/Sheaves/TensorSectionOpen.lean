import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.MixedLocalExtension
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorFramePure

namespace OAI


                                           
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma local_section_coefficient (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    coefficient (tensorFrame L M U e d) (restrictSection U.ι (tensorSection s t)) =
      coefficient e (restrictSection U.ι s) * coefficient d (restrictSection U.ι t) := by
  change (tensorFrame L M U e d).hom.app ⊤
    ((tensorSection s t).app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ (s.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))))) *
    (show Γ(U.toScheme,⊤) from d.hom.app ⊤ (t.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))))
  rw [map_one]
  exact (congrArg (fun value => (tensorFrame L M U e d).hom.app ⊤ value)
    (section_apply s t _)).trans
    (local_framed_pure L M U e d ⊤ _ _)

lemma section_open (L M : LineBundle X) (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    isoOpen (tensorSection s t) = isoOpen s ⊓ isoOpen t := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (tensorSection s t) =
      U.1.ι ⁻¹ᵁ (isoOpen s ⊓ isoOpen t) := by
    refine (preimage_isoOpen (tensorSection s t) U.1.ι (tensorFrame L M U.1 e d)).trans ?_
    refine (congrArg (fun value : Γ(U.1.toScheme,⊤) => U.1.toScheme.basicOpen value)
      (local_section_coefficient L M U.1 e d s t)).trans ?_
    rw [Scheme.basicOpen_mul]
    change _ = (U.1.ι ⁻¹ᵁ isoOpen s) ⊓ (U.1.ι ⁻¹ᵁ isoOpen t)
    exact congrArg₂ (fun left right : U.1.toScheme.Opens => left ⊓ right)
      (preimage_isoOpen s U.1.ι e).symm (preimage_isoOpen t U.1.ι d).symm
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end
end MaximalSeshadri.TensorPure

end

end OAI
